{
  pkgs,
  leanToolchain,
  heronSource,
  lint-driver,
  heron-scan-unwrapped,
  heron-lean-server,
  heron-lsp-probe,
}:
let
  runInConsumerFixture =
    {
      name,
      fixture ? "consumer",
      heronArtifacts ? null,
      script,
      scriptArgs ? [ ],
    }:
    pkgs.stdenv.mkDerivation {
      inherit name;
      src = heronSource;
      TZDIR = "${pkgs.tzdata}/share/zoneinfo";
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
        cd tests/end-to-end/${fixture}
        nu ../${script} ${pkgs.lib.escapeShellArgs scriptArgs}
        runHook postBuild
      '';
      installPhase = "touch $out";
    };

  editorProbeArgs =
    file: probeFlags:
    [
      "${heron-lsp-probe}/bin/heron-lsp-probe"
      "${pkgs.lib.getExe heron-lean-server}"
      file
    ]
    ++ probeFlags;
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

  test-editor-without-project-changes = runInConsumerFixture {
    name = "test-editor-without-project-changes";
    fixture = "vanilla";
    script = "editor-diagnostics.nu";
    scriptArgs = editorProbeArgs "Vanilla/Basic.lean" [
      "--expect"
      "Merge intros"
      "--expect"
      "mut"
      "--expect-quick-fix"
      "--reject"
      "increment (x : Nat)"
    ];
  };

  test-editor-with-plugin-in-lakefile = runInConsumerFixture {
    name = "test-editor-with-plugin-in-lakefile";
    heronArtifacts = lint-driver;
    script = "editor-diagnostics.nu";
    scriptArgs = editorProbeArgs "Consumer/Basic.lean" [
      "--reject"
      "Merge intros"
    ];
  };
}
