{
  pkgs,
  leanToolchain,
  heronSource,
  lint-driver,
  heron-scan-unwrapped,
}:
let
  runInConsumerFixture =
    {
      name,
      heronArtifacts ? null,
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
        ${pkgs.lib.optionalString (heronArtifacts != null) ''
          cp -R ${heronArtifacts}/.lake .
          chmod -R +w .lake
        ''}
        cd tests/end-to-end/consumer
        nu ../${script} ${pkgs.lib.escapeShellArgs scriptArgs}
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
    scriptArgs = [ "../expected-fixes.json" ];
  };

  test-heron-scan = runInConsumerFixture {
    name = "test-heron-scan";
    heronArtifacts = heron-scan-unwrapped;
    script = "heron-scan.nu";
    scriptArgs = [
      "../expected-fixes.json"
      "${heron-scan-unwrapped}/bin/heron-scan"
    ];
  };

  test-plugin-cold-build = runInConsumerFixture {
    name = "test-plugin-cold-build";
    script = "plugin-cold-build.nu";
  };
}
