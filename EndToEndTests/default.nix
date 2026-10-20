{
  pkgs,
  lake2nix,
  heronSource,
  heron-build,
  heron,
  lakeDeps,
  runsEditorProbes,
}:
let
  runScenarioCheck =
    {
      name,
      scenario,
      heronDependency ? heronSource,
      checkArgs ? [ ],
    }:
    lake2nix.mkPackage {
      inherit name;
      src = "${heronSource}/EndToEndTests/${scenario}";
      lakeDeps = lakeDeps // {
        heron = heronDependency;
      };
      TZDIR = "${pkgs.tzdata}/share/zoneinfo";
      postConfigure = "chmod -R u+w .lake/packages/heron";
      buildPhase = ''
        runHook preBuild
        lean --run ${heronSource}/EndToEndTests/ScenarioCheck.lean ${name} ${
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
      "${heronSource}/EndToEndTests/expected-fixes.json"
      "--heron"
      (pkgs.lib.getExe heron)
    ];
  };

  per-file-import = runScenarioCheck {
    name = "per-file-import";
    scenario = "PerFileImport";
    heronDependency = heron-build;
  };
}
