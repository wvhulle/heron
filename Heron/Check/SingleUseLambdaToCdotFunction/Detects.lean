module

meta import Heron.Assert
meta import Heron.Check.SingleUseLambdaToCdotFunction

#assertCheck singleUseLambdaToCdotFunction in
  def f :=
    List.map (fun x => x + 1) [1, 2, 3] becomes
  `(def f :=
    List.map (· + 1) [1, 2, 3])

#assertCheck singleUseLambdaToCdotFunction in
  def g :=
    List.filter (fun x => x > 0) [1, 2, 3] becomes
  `(def g :=
    List.filter (· > 0) [1, 2, 3])

-- Unparenthesised lambda site: the fix must add its own parens, else the bare
-- `· + 1` mis-parses / rescopes `·`.
#assertCheck singleUseLambdaToCdotFunction in
  def h := fun x => x + 1 becomes
  `(def h := (· + 1))

#assertCheck singleUseLambdaToCdotFunction in
  def innerLambdaReusesTheName :=
    List.map (fun x => x + (fun x => x) 1) [1, 2] becomes
  `(def innerLambdaReusesTheName :=
    List.map (· + (fun x => x) 1) [1, 2])

#assertCheck singleUseLambdaToCdotFunction in
def longWords (words : List String) := words.filter fun w => w.length > 4
becomes `(command| def longWords (words : List String) := words.filter (·.length > 4))

#assertCheck singleUseLambdaToCdotFunction in
def prefixes (words : List String) := words.map fun w => w.take 2
becomes `(command| def prefixes (words : List String) := words.map (·.take 2))

#assertCheck singleUseLambdaToCdotFunction in
def longWordsAscii (words : List String) := words.filter fun w => w.length >= 5
becomes `(command| def longWordsAscii (words : List String) := words.filter (·.length >= 5))

#assertCheck singleUseLambdaToCdotFunction in
def doBody : List (IO Nat) := [1, 2].map fun n => do
  IO.println "step"
  pure n
becomes `(command| def doBody : List (IO Nat) := [1, 2].map (do
  IO.println "step"
  pure ·))

#assertCheck singleUseLambdaToCdotFunction in
def letBody := [1, 2].map fun n =>
  let doubled := n * 2
  doubled + 1
becomes `(command| def letBody := [1, 2].map (
  let doubled := · * 2
  doubled + 1))

#assertCheck singleUseLambdaToCdotFunction in
def structureBody := [1, 2].map fun n => { fst := n, snd := 0 : Nat × Nat }
becomes `(command| def structureBody := [1, 2].map ({ fst := ·, snd := 0 : Nat × Nat }))
