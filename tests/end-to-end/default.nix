{
  pkgs,
  leanToolchain,
  heronSource,
  lint-driver,
}:
let
  runInConsumerFixture =
    {
      name,
      heronArtifacts,
      script,
      scriptArgs ? [ ],
    }:
    pkgs.stdenv.mkDerivation {
      inherit name;
      src = heronSource;
      nativeBuildInputs = [
        leanToolchain
        pkgs.nushell
      ];
      buildPhase = ''
        runHook preBuild
        cp -R ${heronArtifacts}/.lake .
        chmod -R +w .lake
        cd tests/end-to-end/consumer
        nu ../${script} ../expected-fixes.json ${pkgs.lib.escapeShellArgs scriptArgs}
        runHook postBuild
      '';
      installPhase = "touch $out";
    };
in
{
  test-plugin-and-lake-lint = runInConsumerFixture {
    name = "test-plugin-and-lake-lint";
    heronArtifacts = lint-driver;
    script = "plugin-and-lake-lint.nu";
  };
}
