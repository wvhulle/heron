module

-- Checks
public import Heron.Check.MergeConsecutiveIntros
public import Heron.Check.RemoveIdRunWithoutEffects
public import Heron.Check.RemoveMutWithoutReassignment
public import Heron.Check.MatchOnBoolToIfThenElse
public import Heron.Check.MergeMatchArmsWithSameBody
public import Heron.Check.MergeBindersWithSameType
public import Heron.Check.NestedMonadToTransformer
public import Heron.Check.RemoveLetWildcardOnUnitAction
public import Heron.Check.TupleMatchToSimultaneousMatch
public import Heron.Check.WildcardMatchToIfLet
public import Heron.Check.AdjacentGetSetToModify
public import Heron.Check.RemoveElsePureUnit
public import Heron.Check.NegatedIfToUnless
public import Heron.Check.NatConstructorsToLiterals
public import Heron.Check.LambdaMatchToPatternMatchingLambda
public import Heron.Check.NestedExprAppToMkAppN
public import Heron.Check.SingleUseLambdaToCdotFunction
public import Heron.Check.LambdaToEtaReducedFunction
public import Heron.Check.LambdaSymbolToFun
public import Heron.Check.StringConcatenationToInterpolation
public import Heron.Check.SingleUseBindToNestedAction
public import Heron.Check.QualifiedConstructorToLeadingDot
public import Heron.Check.MatchOnParametersToPatternMatchingDefinition
public import Heron.Check.ListMapMapToSingleMap
public import Heron.Check.ListMapIdToList
public import Heron.Check.ListReverseReverseToList
public import Heron.Check.ListHeadOfReverseToGetLast
public import Heron.Check.ListAnyOfMapToComposedAny
public import Heron.Check.ListAllOfMapToComposedAll
public import Heron.Check.ListMapOfReplicateToReplicate
public import Heron.Check.OptionMapMapToSingleMap
public import Heron.Check.IdApplicationToArgument
public import Heron.Check.ListFlattenOfMapToFlatMap
-- Refactors
public import Heron.Refactor.FlipIf
public import Heron.Refactor.Inline
public import Heron.Refactor.BindToDo
public import Heron.Refactor.InlineAll
