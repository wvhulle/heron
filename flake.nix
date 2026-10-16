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
      pkgs = import nixpkgs {
        inherit system;
        overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
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
    in
    {
      packages.${system} = {
        inherit
          library
          lint-driver
          heron-scan-unwrapped
          dump-ast
          ;
        heron-scan = heronScanInProject;
        default = heronScanInProject;
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
