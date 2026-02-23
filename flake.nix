{

  nixConfig = {
    extra-substituters = [ "https://wvhulle.cachix.org" ];
    extra-trusted-public-keys = [ "wvhulle.cachix.org-1:heXx8DZMiRsKUx6l1TxNoF+Nmtmz66QEdsonQzc1ir0=" ];
  };
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    lean4.url = "github:wvhulle/lean4";
    lean4-nix.url = "github:lenianiva/lean4-nix";
    tree-sitter-lean.url = "github:wvhulle/tree-sitter-lean";
  };

  outputs =    {
      self,
      nixpkgs,
      lean4,
      lean4-nix,
      tree-sitter-lean,
    }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs {
        inherit system;
        # config.allowUnfree = true;
      };

      lake2nix = pkgs.callPackage lean4-nix.lake {
        lean = {
          lean-all = lean4.packages.${system}.lake;
        };
      };

      tree-sitter-lean-grammar = tree-sitter-lean.packages.${system}.default;

      yamlFormat = pkgs.formats.yaml { };

      sgconfigFile = yamlFormat.generate "sgconfig.yml" {
        ruleDirs = [ "rules" ];
        testConfigs = [ { testDir = "rule-tests"; } ];
        customLanguages.lean = {
          libraryPath = "${tree-sitter-lean-grammar}/lean.so";
          extensions = [ "lean" ];
          expandoChar = "_";
        };
      };
    in
    {
      packages.${system}.default = lake2nix.mkPackage {
        name = "Heron";
        src = ./.;
      };

      devShells.${system} = {
        nix = pkgs.mkShell {
          packages = [
            lean4.packages.${system}.lake
            pkgs.ast-grep
          ];

          shellHook = "ln -sf ${sgconfigFile} sgconfig.yml";
        };

        # Use locally-built lean4 — no flake rebuild on source changes.
        # Requires: make -j -C ../lean4/build/release
        default = pkgs.mkShell {
          packages = with pkgs; [
            ast-grep
            gcc
            llvmPackages.bintools
          ];

          shellHook = ''
            ln -sf ${sgconfigFile} sgconfig.yml
            export PATH="$PWD/../lean4/build/release/stage1/bin:$PATH"
          '';
        };
      };
    };
}
