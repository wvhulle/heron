# No project changes

`heron scan` runs Heron on a Lean project that has never heard of it, without a `require`, plugin
or `import`.

## On the command line: `heron scan`

Build your project, then run `heron scan` in its root directory, from the Heron ref that matches
your toolchain. It re-elaborates the files itself, so it is slower than the lakefile setup on large
projects.

```sh
lake build
nix run github:wvhulle/heron/main -- scan Consumer        # check a library or directory
nix run github:wvhulle/heron/main -- scan --fix Foo.lean  # apply fixes
```

A project that requires Heron can also run it as `lake exe heron scan`:

```sh
lake exe heron scan --fix Foo/Bar.lean
echo 'def f := fun x => x + 1' | lake exe heron scan -
```

It accepts `--json`, `--fix`, `--apply`, `--color` and `--no-color`, plus `--per-file`,
`--no-cache` and `--no-parallel`, and reads stdin with `-`. `--rule <names>` runs only the named
checks, separated by commas. `heron rules` lists every check and refactor with its description and
sources; with `--json` it prints them as a JSON array. A check that flags code without a fix
is reported like any other finding; in `--json` output such a finding has no `after` field.
