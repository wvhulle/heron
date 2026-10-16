use ../reported-fixes.nu [parse-reported-fixes assert-matches-expected]

def main [expected_fixes: path, heron_scan: path]: nothing -> nothing {
  lake build
  ^$heron_scan --no-cache --json Consumer
  | parse-reported-fixes heron-scan
  | assert-matches-expected $expected_fixes
}
