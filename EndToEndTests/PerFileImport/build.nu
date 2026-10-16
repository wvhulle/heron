def main []: nothing -> nothing {
  let build = (lake build | complete)
  let build_log = $"($build.stdout)($build.stderr)"
  print $build_log
  if $build.exit_code != 0 {
    error make {msg: "lake build of the per-file import fixture failed"}
  }
  if not ($build_log | str contains "ImportingLibrary/Basic.lean") or not ($build_log | str contains "Merge intros") {
    error make {msg: "lake build did not report Heron's hint for the file that imports Heron"}
  }
}
