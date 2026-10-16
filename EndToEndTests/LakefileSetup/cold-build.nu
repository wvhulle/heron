def main []: nothing -> nothing {
  let build = (lake build | complete)
  let build_log = $"($build.stdout)($build.stderr)"
  print $build_log
  let repeated_heron_jobs = (
    $build_log
    | parse --regex '(?:Built|Replayed|Building) (?<job>Heron\S*)'
    | get job
    | uniq --count
    | where count > 1
  )
  if ($repeated_heron_jobs | is-not-empty) {
    error make {
      msg: ([
        "Lake ran these Heron jobs more than once, so concurrent duplicates can corrupt the build:"
        ($repeated_heron_jobs | to text)
      ] | str join "\n")
    }
  }
  if $build.exit_code != 0 {
    error make {msg: "cold lake build of the consumer fixture failed"}
  }
}
