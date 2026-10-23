lean4-nix:
(import "${lean4-nix}/manifests/v4.34.0.nix")
// {
  tag = "v4.34.1";
  rev = "5045d0056413266e57c625dcd7c365b10e377c52";
  toolchain = {
    x86_64-linux = {
      url = "https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst";
      hash = "sha256-R79LvXj3DC6WcFmKtxJNkrbvtzMP8z5fu0Aw9v1y5OQ=";
    };
  };
}
