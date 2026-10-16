def main [editor_probe: path, heron_language_server: path]: nothing -> nothing {
  lake build
  lean --run $editor_probe Consumer/Basic.lean --expect "Merge intros" --expect mut --expect-quick-fix -- lake serve
  lean --run $editor_probe Consumer/Basic.lean --reject "Merge intros" -- $heron_language_server
}
