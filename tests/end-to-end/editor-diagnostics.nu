def --wrapped main [probe: path, server: path, file: string, ...probe_flags: string]: nothing -> nothing {
  lake build
  ^$probe $file ...$probe_flags -- $server
}
