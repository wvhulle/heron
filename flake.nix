{

  nixConfig = {
    extra-substituters = [ "https://wvhulle.cachix.org" ];
    extra-trusted-public-keys = [ "wvhulle.cachix.org-1:heXx8DZMiRsKUx6l1TxNoF+Nmtmz66QEdsonQzc1ir0=" ];
  };
  inputs = {
    lean4.url = "github:wvhulle/lean4";
    lean4-nix.url = "github:lenianiva/lean4-nix";
    nixpkgs.follows = "lean4-nix/nixpkgs";
  };

  outputs =
    {
      nixpkgs,
      lean4,
      lean4-nix,
      ...
    }:
    let
      system = "x86_64-linux";

      pkgs = import nixpkgs { inherit system; };

      forkLean = lean4.packages.${system}.lake;

      lake2nix = pkgs.callPackage lean4-nix.lake {
        lean.lean-all = forkLean;
      };

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

      developer-tools = buildLakeTargets {
        name = "heron-developer-tools";
        targets = "dump-syntax-tree DeveloperTools.RuleShowcase";
        lakeArtifacts = library;
      };

      heronScanInProject = pkgs.writeShellApplication {
        name = "heron-scan";
        runtimeInputs = [ forkLean ];
        text = ''exec lake env ${heron-scan-unwrapped}/bin/heron-scan "$@"'';
      };

      language-server-build = buildLakeTargets {
        name = "heron-language-server-build";
        targets = "heron-language-server";
        lakeArtifacts = library;
      };

      heron-language-server =
        pkgs.runCommand "heron-language-server" { meta.mainProgram = "heron-language-server"; }
          ''
            install -Dm755 ${language-server-build}/.lake/build/bin/heron-language-server $out/bin/heron-language-server
            install -Dm644 ${language-server-build}/.lake/build/lib/libheron_Heron.so $out/lib/libheron_Heron.so
          '';
    in
    {
      packages.${system} = {
        inherit heron-language-server;
        heron-scan = heronScanInProject;
        default = heronScanInProject;
      };

      homeModules.default =
        { config, lib, ... }:
        {
          options.programs.heron.enable =
            lib.mkEnableOption "a second Lean language server with Heron's hints and quick fixes for every Lake project";

          config = lib.mkIf config.programs.heron.enable {
            services.toolchain.langs.lean.servers.heron.package = heron-language-server;
          };
        };

      checks.${system} = {
        rules = library;
        inherit developer-tools;
      }
      // import ./EndToEndTests {
        inherit
          pkgs
          lint-driver
          heron-language-server
          ;
        heron-scan = heronScanInProject;
        leanToolchain = forkLean;
        heronSource = ./.;
      };

      devShells.${system} = rec {
        managed-fork = pkgs.mkShell {
          packages = [ forkLean ];
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

        default = unmanaged-fork;
      };
    };
}
