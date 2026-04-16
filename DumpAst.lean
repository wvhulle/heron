import Lean

open Lean Parser

/-- Convert a syntax tree to a `Json` value. -/
partial def syntaxToJson (stx : Syntax) : Json :=
  match stx with
  | .missing => Json.mkObj [("type", "missing")]
  | .atom _ val => Json.mkObj [("type", "atom"), ("val", val)]
  | .ident _ _ val _ => Json.mkObj [("type", "ident"), ("name", val.toString)]
  | .node _ kind args =>
    let shortKind := (kind.replacePrefix `Lean.Parser Name.anonymous).toString
    Json.mkObj
      [("type", "node"), ("kind", shortKind),
        ("children",
          Json.arr (args.mapIdx fun i child => Json.mkObj [("index", (i : Nat)), ("value", syntaxToJson child)]))]

def main (args : List String) : IO Unit := do
  let env ← mkEmptyEnvironment
  let input ←
    match args with
    | ["--input", input] =>
      pure input
    | [filepath] =>
      IO.FS.readFile filepath
    | [] =>
      readStdin
    | _ =>
      do
        IO.eprintln "Usage: dump-ast [--input <string> | <file> | stdin]"
        IO.Process.exit 1
  match runParserCategory env `command input with
  | .ok stx =>
    IO.println (syntaxToJson stx).pretty
  | .error msg =>
    IO.eprintln s! "Parse error: {msg}"
    IO.Process.exit 1
where readStdin : IO String := do
    let stdin ← IO.getStdin
    let mut result := ""
    let mut done := false
    while !done do
      let line ← stdin.getLine
      if line.isEmpty then 
        done := true
      else
        result := result ++ line
    pure result
