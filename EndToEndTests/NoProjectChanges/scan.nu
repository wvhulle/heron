use ../reported-fixes.nu [parse-reported-fixes assert-matches-expected]

def assert-lists-rules [heron_scan: path]: nothing -> nothing {
  let listed = ^$heron_scan rules --json | from json
  let kinds = $listed | get kind | uniq | sort
  if $kinds != [check refactor] {
    error make { msg: $"heron-scan rules lists kinds ($kinds), expected both check and refactor" }
  }
  let missing = $listed | where description == "" | get name
  if ($missing | is-not-empty) {
    error make { msg: $"heron-scan rules lists rules without a description: ($missing)" }
  }
}

def main [expected_fixes: path, heron_scan: path]: nothing -> nothing {
  lake build
  assert-lists-rules $heron_scan
  ^$heron_scan --no-cache --json Consumer
  | parse-reported-fixes heron-scan
  | assert-matches-expected $expected_fixes
}
