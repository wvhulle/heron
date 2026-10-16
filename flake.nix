{

  nixConfig = {
    extra-substituters = [ "https://wvhulle.cachix.org" ];
    extra-trusted-public-keys = [ "wvhulle.cachix.org-1:heXx8DZMiRsKUx6l1TxNoF+Nmtmz66QEdsonQzc1ir0=" ];
  };
  inputs = {
    lean4-nix.url = "github:lenianiva/lean4-nix";
    nixpkgs.follows = "lean4-nix/nixpkgs";
  };

  outputs =
    {
      nixpkgs,
      lean4-nix,
      ...
    }:
    let
      system = "x86_64-linux";

      toolchainTag = builtins.head (
        builtins.match "[[:space:]]*leanprover/lean4:([^[:space:]]+)[[:space:]]*" (
          builtins.readFile ./lean-toolchain
        )
      );

      vendoredManifestOverlay =
        manifest: final: prev:
        (manifest.overlay final prev)
        // {
          lean = (final.callPackage "${lean4-nix}/lib/toolchain.nix" { }).fetchBinaryLean manifest;
        };

      leanOverlay =
        if lean4-nix.tags ? ${toolchainTag} then
          lean4-nix.readToolchainFile ./lean-toolchain
        else
          vendoredManifestOverlay (import ./nix/lean4-nix-manifests/${toolchainTag}.nix lean4-nix);

      pkgs = import nixpkgs {
        inherit system;
        overlays = [ leanOverlay ];
      };

      lake2nix = pkgs.callPackage lean4-nix.lake { };

      lakeDeps = lake2nix.buildDeps { src = ./.; };

      buildLakeTargets =
        {
          name,
          targets,
          lakeArtifacts ? null,
        }:
        lake2nix.mkPackage (
          {
            inherit name lakeDeps;
            src = ./.;
            installArtifacts = true;
            buildPhase = ''
              runHook preBuild
              lake build ${targets}
              runHook postBuild
            '';
          }
          // pkgs.lib.optionalAttrs (lakeArtifacts != null) { inherit lakeArtifacts; }
        );

      library = buildLakeTargets {
        name = "heron-library";
        targets = "Heron Heron:shared";
      };

      lint-driver = buildLakeTargets {
        name = "heron-lint-driver";
        targets = "heron";
        lakeArtifacts = library;
      };

      heron-scan-unwrapped = buildLakeTargets {
        name = "heron-scan-unwrapped";
        targets = "heron-scan";
        lakeArtifacts = library;
      };

      dump-ast = buildLakeTargets {
        name = "heron-dump-ast";
        targets = "dump-ast";
        lakeArtifacts = library;
      };

      heronScanInProject = pkgs.writeShellApplication {
        name = "heron-scan";
        runtimeInputs = [ pkgs.lean.lean-all ];
        text = ''exec lake env ${heron-scan-unwrapped}/bin/heron-scan "$@"'';
      };

      lean-server-build = buildLakeTargets {
        name = "heron-lean-server-build";
        targets = "heron-lean-server";
        lakeArtifacts = library;
      };

      heron-lean-server =
        pkgs.runCommand "heron-lean-server" { meta.mainProgram = "heron-lean-server"; }
          ''
            install -Dm755 ${lean-server-build}/.lake/build/bin/heron-lean-server $out/bin/heron-lean-server
            install -Dm644 ${lean-server-build}/.lake/build/lib/libheron_Heron.so $out/lib/libheron_Heron.so
          '';

      heron-lsp-probe = buildLakeTargets {
        name = "heron-lsp-probe";
        targets = "heron-lsp-probe";
      };
    in
    {
      packages.${system} = {
        inherit
          library
          lint-driver
          heron-scan-unwrapped
          dump-ast
          heron-lean-server
          heron-lsp-probe
          ;
        heron-scan = heronScanInProject;
        default = heronScanInProject;
      };

      homeModules.default =
        { config, lib, ... }:
        {
          options.programs.heron.enable =
            lib.mkEnableOption "a second Lean language server with Heron's hints and quick fixes for every Lake project";

          config = lib.mkIf config.programs.heron.enable {
            services.toolchain.langs.lean.servers.heron.package = heron-lean-server;
          };
        };

      apps.${system} = rec {
        heron-scan = {
          type = "app";
          program = "${heronScanInProject}/bin/heron-scan";
        };
        default = heron-scan;
      };

      checks.${system} = {
        build-library-with-rule-tests = library;
        build-lint-driver = lint-driver;
        build-heron-scan = heron-scan-unwrapped;
        build-dump-ast = dump-ast;
        build-heron-scan-app = heronScanInProject;
        build-heron-lean-server = heron-lean-server;
        build-heron-lsp-probe = heron-lsp-probe;
      }
      // import ./tests/end-to-end {
        inherit
          pkgs
          lint-driver
          heron-scan-unwrapped
          heron-lean-server
          heron-lsp-probe
          ;
        leanToolchain = pkgs.lean.lean-all;
        heronSource = ./.;
      };

      devShells.${system} = rec {
        managed-stock = pkgs.mkShell {
          packages = [ pkgs.lean.lean-all ];
        };

        # Standard Lean via elan — unmanaged, for building the vanilla Heron target.
        unmanaged-vanilla = pkgs.mkShell {
          packages = [
            pkgs.elan
          ];
        };

        # Use locally-built lean4 — no flake rebuild on source changes.
        # Requires: cd ../lean4 && cmake --preset release && make -C build/release
        # And, for lsp-probe: cd ../lean4/script && lake build lsp-probe
        unmanaged-fork =
          let
            lsp-probe = pkgs.writeShellScriptBin "lsp-probe" ''
              exec "$PWD/../lean4/script/.lake/build/bin/lsp-probe" "$@"
            '';
          in
          pkgs.mkShell {
            packages = with pkgs; [
              gcc
              llvmPackages.bintools
              lsp-probe
            ];

            shellHook = ''
              export ELAN=""
              export PATH="$PWD/../lean4/build/release/bin:$PATH"
            '';
          };

        default = unmanaged-vanilla;
      };
    };
}
