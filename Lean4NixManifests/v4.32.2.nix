lean4-nix:
(import "${lean4-nix}/manifests/v4.32.0.nix")
// {
  tag = "v4.32.2";
  rev = "f3b06c705e6c85f5314019d5d3baab0fec5b580c";
  toolchain = {
    x86_64-linux = {
      url = "https://github.com/leanprover/lean4/releases/download/v4.32.2/lean-4.32.2-linux.tar.zst";
      hash = "sha256-XyBp5vXbc3gPN0zLSc6OpkmqIKDOvwEWgWdEyZnOcqo=";
    };
  };
}
