module

-- Checks
public import Heron.Check.RflToExactRfl
public import Heron.Check.MergeIntros
public import Heron.Check.UnnecessaryIdRun
public import Heron.Check.UnnecessaryMut
public import Heron.Check.BoolMatchToIf
public import Heron.Check.DuplicateAltToOrPattern
public import Heron.Check.MergeBinders
public import Heron.Check.NestedMonadToJoin
public import Heron.Check.NestedMonadToTransformer
public import Heron.Check.RedundantLetWildcard
public import Heron.Check.TupleMatchToSimultaneous
public import Heron.Check.MatchToIfLet
public import Heron.Check.GetSetToModify
public import Heron.Check.RedundantElsePureUnit
public import Heron.Check.IfNotToUnless
public import Heron.Check.NatLiteralPatterns
public import Heron.Check.FunMatchToMatchFun
public import Heron.Check.ExprAppChainToMkAppN
public import Heron.Check.FunToCdot
public import Heron.Check.UnusedImport
public import Heron.Check.UnnecessaryPublicImport
public import Heron.Check.UnnecessaryMetaImport
-- Refactors
public import Heron.Refactor.FlipIf
public import Heron.Refactor.Inline
public import Heron.Refactor.BindToDo
public import Heron.Refactor.InlineAll
