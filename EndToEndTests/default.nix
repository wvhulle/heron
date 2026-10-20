{
  pkgs,
  leanToolchain,
  heronSource,
  lint-driver,
  heron-language-server,
  runsEditorProbes,
}:
let
  runScenarioCheck =
    {
      name,
      scenario,
      heronArtifacts ? null,
      checkArgs ? [ ],
    }:
    pkgs.stdenv.mkDerivation {
      inherit name;
      src = heronSource;
      TZDIR = "${pkgs.tzdata}/share/zoneinfo";
      nativeBuildInputs = [ leanToolchain ];
      buildPhase = ''
        runHook preBuild
        ${pkgs.lib.optionalString (heronArtifacts != null) ''
          cp -R ${heronArtifacts}/.lake .
          chmod -R +w .lake
        ''}
        cd EndToEndTests/${scenario}
        lean --run ../ScenarioCheck.lean ${name} ${
          pkgs.lib.escapeShellArgs (checkArgs ++ pkgs.lib.optional (!runsEditorProbes) "--skip-editor-probes")
        }
        runHook postBuild
      '';
      installPhase = "touch $out";
    };
in
{
  lakefile-setup = runScenarioCheck {
    name = "lakefile-setup";
    scenario = "LakefileSetup";
    checkArgs = [
      "--expected-fixes"
      "../expected-fixes.json"
      "--language-server"
      (pkgs.lib.getExe heron-language-server)
    ];
  };

  per-file-import = runScenarioCheck {
    name = "per-file-import";
    scenario = "PerFileImport";
    heronArtifacts = lint-driver;
  };
}
