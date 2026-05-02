{

  nixConfig = {
    extra-substituters = [ "https://wvhulle.cachix.org" ];
    extra-trusted-public-keys = [ "wvhulle.cachix.org-1:heXx8DZMiRsKUx6l1TxNoF+Nmtmz66QEdsonQzc1ir0=" ];
  };
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    lean4 = {

      # url = "github:wvhulle/lean4";

      url = "git+file:/home/wvhulle/Code/lean4";
    };
    lean4-nix.url = "github:lenianiva/lean4-nix";
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
      pkgs = import nixpkgs {
        inherit system;
      };

      lake2nix = pkgs.callPackage lean4-nix.lake {
        lean = {
          lean-all = lean4.packages.${system}.lake;
        };
      };

      lakeDeps = lake2nix.buildDeps { src = ./.; };

      heron = lake2nix.mkPackage {
        name = "Heron";
        src = ./.;
        inherit lakeDeps;
        installArtifacts = true;
      };

      deadheron = lake2nix.mkPackage {
        name = "DeadHeron";
        src = ./.;
        inherit lakeDeps;
        lakeArtifacts = heron;
      };
    in
    {
      packages.${system} = {
        inherit heron deadheron;
        default = deadheron;
      };

      devShells.${system} = rec {
        # Fork lean managed by Nix flake input.
        managed-fork = pkgs.mkShell {
          packages = [
            lean4.packages.${system}.lake
          ];
        };

        # Standard Lean via elan — unmanaged, for building the vanilla Heron target.
        unmanaged-vanilla = pkgs.mkShell {
          packages = [
            pkgs.elan
          ];
        };

        # Use locally-built lean4 — no flake rebuild on source changes.
        # Requires: cd ../lean4 && cmake --preset release && make -C build/release
        unmanaged-fork = pkgs.mkShell {
          packages = with pkgs; [
            gcc
            llvmPackages.bintools
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
