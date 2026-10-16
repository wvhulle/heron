use reported-fixes.nu [parse-reported-fixes assert-matches-expected]

def main [expected_fixes: path]: nothing -> nothing {
  let build = (lake build | complete)
  let build_log = $"($build.stdout)($build.stderr)"
  print $build_log
  if $build.exit_code != 0 {
    error make {msg: "lake build of the consumer fixture failed"}
  }
  if not ($build_log | str contains "warning: Consumer/Basic.lean") {
    error make {
      msg: "lake build did not report Heron diagnostics, so the plugin was not loaded"
    }
  }
  lake lint -- --json
  | parse-reported-fixes "lake lint"
  | assert-matches-expected $expected_fixes
}
