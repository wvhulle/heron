def main [editor_probe: path]: nothing -> nothing {
  lake build
  lean --run $editor_probe ImportingLibrary/Basic.lean --expect "Merge intros" --expect-quick-fix -- lake serve
}
