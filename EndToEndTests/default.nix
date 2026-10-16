{
  pkgs,
  leanToolchain,
  heronSource,
  lint-driver,
  heron-scan,
  heron-language-server,
}:
let
  runScenarioScript =
    {
      name,
      scenario,
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
        cd EndToEndTests/${scenario}
        nu ${script} ${pkgs.lib.escapeShellArgs scriptArgs}
        runHook postBuild
      '';
      installPhase = "touch $out";
    };

  editorProbe = "../EditorProbe.lean";
  languageServer = pkgs.lib.getExe heron-language-server;
in
{
  lakefile-setup-build-and-lint = runScenarioScript {
    name = "lakefile-setup-build-and-lint";
    scenario = "LakefileSetup";
    heronArtifacts = lint-driver;
    script = "build-and-lint.nu";
    scriptArgs = [ "../expected-fixes.json" ];
  };

  lakefile-setup-cold-build = runScenarioScript {
    name = "lakefile-setup-cold-build";
    scenario = "LakefileSetup";
    script = "cold-build.nu";
  };

  lakefile-setup-editor = runScenarioScript {
    name = "lakefile-setup-editor";
    scenario = "LakefileSetup";
    heronArtifacts = lint-driver;
    script = "editor.nu";
    scriptArgs = [
      editorProbe
      languageServer
    ];
  };

  per-file-import-build = runScenarioScript {
    name = "per-file-import-build";
    scenario = "PerFileImport";
    heronArtifacts = lint-driver;
    script = "build.nu";
  };

  per-file-import-editor = runScenarioScript {
    name = "per-file-import-editor";
    scenario = "PerFileImport";
    heronArtifacts = lint-driver;
    script = "editor.nu";
    scriptArgs = [ editorProbe ];
  };

  no-project-changes-scan = runScenarioScript {
    name = "no-project-changes-scan";
    scenario = "NoProjectChanges";
    script = "scan.nu";
    scriptArgs = [
      "../expected-fixes.json"
      (pkgs.lib.getExe heron-scan)
    ];
  };

  no-project-changes-editor = runScenarioScript {
    name = "no-project-changes-editor";
    scenario = "NoProjectChanges";
    script = "editor.nu";
    scriptArgs = [
      editorProbe
      languageServer
    ];
  };
}
