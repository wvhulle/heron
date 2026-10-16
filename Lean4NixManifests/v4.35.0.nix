lean4-nix:
(import "${lean4-nix}/manifests/v4.34.0.nix")
// {
  tag = "v4.35.0";
  rev = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc";
  toolchain = {
    x86_64-linux = {
      url = "https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst";
      hash = "sha256-colZekRUMkbJInuMrlAXZ+CVzhf21Ei5X8So3Jcmj20=";
    };
  };
}
