def normalize []: list<record> -> list<record> {
  each { sort } | sort-by file line col rule
}

export def parse-reported-fixes [reporter: string]: string -> list<record> {
  let output = $in
  try {
    $output | from json
  } catch {
    error make {msg: $"($reporter) did not print a JSON list of fixes:\n($output)"}
  }
}

export def assert-matches-expected [expected_fixes: path]: list<record> -> nothing {
  let reported = ($in | normalize)
  let expected = try {
    open $expected_fixes | normalize
  } catch {
    error make {msg: $"cannot read the expected fixes from ($expected_fixes)"}
  }
  if $reported != $expected {
    error make {
      msg: ([
        $"reported fixes differ from ($expected_fixes)"
        expected:
        ($expected | to json)
        reported:
        ($reported | to json)
      ] | str join "\n")
    }
  }
}
