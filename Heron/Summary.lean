namespace Heron

/-- A column definition for table rendering. -/
structure Column where
  header : String
  separator : Char := '─'

/-- Render a table with auto-expanding columns.
    Column widths expand to fit the widest cell in each column.
    Separator rows fill the full column width with the separator character. -/
def renderTable (columns : Array Column) (rows : Array (Array String)) : String :=
  let gap := 2
  let headers := columns.map (·.header)
  let widths := (#[headers] ++ rows).foldl (init := columns.map fun _ => 0) fun acc row =>
    Array.zipWith max acc (row.map (·.length))
  let pad (s : String) (w : Nat) := s.pushn ' ' (w - s.length + gap)
  let renderRow (cells : Array String) :=
    (Array.zipWith pad cells widths).toList |> String.join
  let sepLine := (Array.zipWith (fun c w => "".pushn c.separator w |>.pushn ' ' gap) columns widths).toList |> String.join
  String.intercalate "\n" ([renderRow headers, sepLine] ++ (rows.map renderRow).toList)

end Heron
