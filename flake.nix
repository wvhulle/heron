{

  nixConfig = {
    extra-substituters = [ "https://wvhulle.cachix.org" ];
    extra-trusted-public-keys = [ "wvhulle.cachix.org-1:heXx8DZMiRsKUx6l1TxNoF+Nmtmz66QEdsonQzc1ir0=" ];
  };
  inputs = {
    lean4-nix.url = "github:lenianiva/lean4-nix";
    nixpkgs.follows = "lean4-nix/nixpkgs";
    weir.url = "git+https://codeberg.org/wvhulle/weir";
    heron-lean-v4-29-1.url = "github:wvhulle/heron?ref=lean/v4.29.1";
    heron-lean-v4-30-0.url = "github:wvhulle/heron?ref=lean/v4.30.0";
    heron-lean-v4-31-0.url = "github:wvhulle/heron?ref=lean/v4.31.0";
    heron-lean-v4-32-0.url = "github:wvhulle/heron?ref=lean/v4.32.0";
    heron-lean-v4-32-2.url = "github:wvhulle/heron?ref=lean/v4.32.2";
    heron-lean-v4-33-0.url = "github:wvhulle/heron?ref=lean/v4.33.0";
    heron-lean-v4-33-1.url = "github:wvhulle/heron?ref=lean/v4.33.1";
    heron-lean-v4-34-0.url = "github:wvhulle/heron?ref=lean/v4.34.0";
    heron-lean-v4-34-1.url = "github:wvhulle/heron?ref=lean/v4.34.1";
  };

  outputs =
    {
      nixpkgs,
      lean4-nix,
      weir,
      ...
    }@inputs:
    let
      system = "x86_64-linux";

      inherit
        (weir.lib.leanProject {
          src = ./.;
          inherit nixpkgs lean4-nix system;
        })
        toolchainTag
        pkgs
        lake2nix
        lakeDeps
        buildLakeTargets
        ;

      library = buildLakeTargets {
        name = "heron-library";
        targets = "Heron Heron:shared";
      };

      heron-build = buildLakeTargets {
        name = "heron-build";
        targets = "heron";
        lakeArtifacts = library;
      };

      developer-tools = buildLakeTargets {
        name = "heron-developer-tools";
        targets = "dump-syntax-tree RuleDevelopment heron-self-lint";
        lakeArtifacts = library;
        afterBuild = "lake exe heron-self-lint";
      };

      heron = weir.lib.bundleReleasePlugins pkgs {
        name = "heron";
        lakeBuild = heron-build;
        pluginFileName = "libheron_Heron.so";
        releases = with inputs; [
          heron-lean-v4-29-1
          heron-lean-v4-30-0
          heron-lean-v4-31-0
          heron-lean-v4-32-0
          heron-lean-v4-32-2
          heron-lean-v4-33-0
          heron-lean-v4-33-1
          heron-lean-v4-34-0
          heron-lean-v4-34-1
        ];
      };
    in
    {
      packages.${system} = {
        inherit heron;
        default = heron;
      };

      homeModules.default = weir.lib.homeModule {
        name = "heron";
        package = heron;
        description = "a second Lean language server with Heron's hints and quick fixes for every Lake project";
      };

      checks.${system} = {
        rules = library;
        inherit developer-tools;
      }
      // import ./EndToEndTests {
        inherit
          pkgs
          lake2nix
          heron-build
          heron
          lakeDeps
          ;
        heronSource = ./.;
        runsEditorProbes = pkgs.lib.versionAtLeast (pkgs.lib.removePrefix "v" toolchainTag) "4.31.0";
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
