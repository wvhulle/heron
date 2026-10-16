def main [probe: path, server: path, file: string]: nothing -> nothing {
  lake build
  ^$probe $file --expect "Merge intros" --expect "mut" --expect-quick-fix -- $server
}
