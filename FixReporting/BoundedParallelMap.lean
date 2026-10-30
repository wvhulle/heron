namespace FixReporting

private partial def drainSharedQueue {Input Output : Type} (inputs : Array Input)
    (process : Input → IO Output) (nextIndex : IO.Ref Nat) (outputs : IO.Ref (Array (Option Output))) :
    IO Unit := do
  let index ← nextIndex.modifyGet fun index => (index, index + 1)
  let some input := inputs[index]? | return
  try
    let output ← process input
    outputs.modify (·.set! index (some output))
  catch _ => pure ()
  drainSharedQueue inputs process nextIndex outputs

def boundedParallelMap {Input Output : Type} (concurrency : Nat) (inputs : Array Input)
    (process : Input → IO Output) : IO (Array Output) := do
  let nextIndex ← IO.mkRef 0
  let outputs ← IO.mkRef (Array.replicate inputs.size none)
  let workers ← (Array.range (min (max 1 concurrency) inputs.size)).mapM fun _ =>
    IO.asTask (drainSharedQueue inputs process nextIndex outputs)
  for worker in workers do
    let _ ← IO.wait worker
  return (← outputs.get).filterMap id

end FixReporting
