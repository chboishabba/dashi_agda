module DASHI.Analysis.RiemannG2PostScalarBalanceBreakingBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleG2CurrentCutExact as Current
import DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact as Scalar

------------------------------------------------------------------------
-- POST-SCALAR BIDI SEAM: BALANCE BREAKING / CHANGED COMPARISON
--
-- User-directed assumption: the ordinary harmonic machinery and the exact
-- same-object scalar attachment are available.  A successful scalar estimate
-- is therefore treated as an input to this stage rather than rebuilt here.
--
-- The current G2 cut already records the kernel-checked obstruction:
-- if projective balance identifies the surviving off-ordinate energy with the
-- cluster margin, that same energy cannot also be strictly below the margin.
-- Hence a stronger estimate on the unchanged comparison object cannot finish
-- the contradiction.  The next theorem-bearing payment is an explicit witness
-- that the final comparison is no longer the unbroken-balance comparison.
------------------------------------------------------------------------

data ComparisonChangeKind : Set where
  explicitBalanceDefect
  changedComparisonObject
  strictOffClusterSeparation
  refinedConsumerWithDifferentMargin
  : ComparisonChangeKind

record LiteralG2ComparisonProblem : Set₁ where
  field
    Scalar : Set
    offEnergy clusterMargin : Scalar
    StrictBelow : Scalar -> Scalar -> Set
    SameComparisonObject : Scalar -> Scalar -> Set

    exactOffEnergyIsLiteralG2OffEnergy : Set
    exactClusterMarginIsLiteralG2ClusterMargin : Set
    exactFinalConsumerParametersUsed : Set

open LiteralG2ComparisonProblem public

record BalanceBreakingReceipt
    (P : LiteralG2ComparisonProblem) : Set₁ where
  field
    changeKind : ComparisonChangeKind
    changedComparisonWitness : Set
    noSilentReuseOfUnbrokenBalance : Set
    consumerReference : String

open BalanceBreakingReceipt public

record UnbrokenProjectiveBalance
    (P : LiteralG2ComparisonProblem) : Set₁ where
  field
    balanceIdentifiesComparison : SameComparisonObject P (offEnergy P) (clusterMargin P)

open UnbrokenProjectiveBalance public

record PostScalarContradictionAdmission
    (scalarProblem : Scalar.LiteralTargetCenteredScalarProblem)
    (comparisonProblem : LiteralG2ComparisonProblem) : Set₁ where
  constructor post-scalar-contradiction-admission
  field
    scalarConsumerClosed : Scalar.G2dScalarConsumerClosure scalarProblem
    balanceBreaking : BalanceBreakingReceipt comparisonProblem
    strictFinalComparison :
      StrictBelow comparisonProblem
        (offEnergy comparisonProblem)
        (clusterMargin comparisonProblem)
    sameLiteralFinalConsumerUsed : Set

open PostScalarContradictionAdmission public

scalarClosureAndBalanceBreakAdmitFinalComparison :
  (S : Scalar.LiteralTargetCenteredScalarProblem) ->
  (P : LiteralG2ComparisonProblem) ->
  Scalar.G2dScalarConsumerClosure S ->
  BalanceBreakingReceipt P ->
  StrictBelow P (offEnergy P) (clusterMargin P) ->
  Set ->
  PostScalarContradictionAdmission S P
scalarClosureAndBalanceBreakAdmitFinalComparison S P scalarClosed break strictBelow sameConsumer =
  post-scalar-contradiction-admission scalarClosed break strictBelow sameConsumer

------------------------------------------------------------------------
-- Search pruning.
--
-- This module intentionally does not manufacture a contradiction from an
-- unbroken balance receipt.  The live current-cut theorem says that route is
-- inadmissible.  Accordingly, "tighten the same scalar estimate again" is not
-- represented as a ComparisonChangeKind at all.
------------------------------------------------------------------------

data PostScalarSearchMove : Set where
  tightenSameScalarEstimate
  exposeBalanceDefect
  changeComparisonObject
  proveStrictOffClusterSeparation
  refineFinalConsumerMargin
  : PostScalarSearchMove

SearchRelevantAfterScalarClosure : PostScalarSearchMove -> Set
SearchRelevantAfterScalarClosure tightenSameScalarEstimate = ⊥
SearchRelevantAfterScalarClosure exposeBalanceDefect = ⊤
SearchRelevantAfterScalarClosure changeComparisonObject = ⊤
SearchRelevantAfterScalarClosure proveStrictOffClusterSeparation = ⊤
SearchRelevantAfterScalarClosure refineFinalConsumerMargin = ⊤

tighteningSameScalarEstimateIsPruned :
  SearchRelevantAfterScalarClosure tightenSameScalarEstimate -> ⊥
tighteningSameScalarEstimateIsPruned x = x

currentProjectiveBalanceNoGoOwned :
  Current.projectiveBalanceStrictInequalityNoGoClosedInAgda
    Current.canonicalAristotleG2CurrentCut ≡ true
currentProjectiveBalanceNoGoOwned =
  Current.projectiveBalanceStrictInequalityNoGoClosedInAgdaIsTrue
    Current.canonicalAristotleG2CurrentCut

currentStrictRouteUnderUnbrokenBalanceIsInadmissible :
  Current.strictOffEnergyBelowClusterUnderUnbrokenBalanceAdmissible
    Current.canonicalAristotleG2CurrentCut ≡ false
currentStrictRouteUnderUnbrokenBalanceIsInadmissible =
  Current.strictOffEnergyBelowClusterUnderUnbrokenBalanceAdmissibleIsFalse
    Current.canonicalAristotleG2CurrentCut

currentBalanceBreakingPremiseRequired :
  Current.balanceBreakingPremiseRequiredForStrictContradictionRoute
    Current.canonicalAristotleG2CurrentCut ≡ true
currentBalanceBreakingPremiseRequired =
  Current.balanceBreakingPremiseRequiredForStrictContradictionRouteIsTrue
    Current.canonicalAristotleG2CurrentCut

record PostScalarBalanceBreakingBoundary : Set where
  constructor post-scalar-balance-breaking-boundary
  field
    ordinaryScalarHarmonicMachineryNeedsFurtherSharpeningHere : Bool
    ordinaryScalarHarmonicMachineryNeedsFurtherSharpeningHereIsFalse :
      ordinaryScalarHarmonicMachineryNeedsFurtherSharpeningHere ≡ false

    scalarClosureAloneAdmitsFinalStrictContradiction : Bool
    scalarClosureAloneAdmitsFinalStrictContradictionIsFalse :
      scalarClosureAloneAdmitsFinalStrictContradiction ≡ false

    unchangedProjectiveBalanceCanBeCombinedWithStrictBelow : Bool
    unchangedProjectiveBalanceCanBeCombinedWithStrictBelowIsFalse :
      unchangedProjectiveBalanceCanBeCombinedWithStrictBelow ≡ false

    explicitComparisonChangeReceiptIsTheNextPayment : Bool
    explicitComparisonChangeReceiptIsTheNextPaymentIsTrue :
      explicitComparisonChangeReceiptIsTheNextPayment ≡ true

    strongerBoundOnSameComparisonIsHighestAlpha : Bool
    strongerBoundOnSameComparisonIsHighestAlphaIsFalse :
      strongerBoundOnSameComparisonIsHighestAlpha ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalPostScalarBalanceBreakingBoundary : PostScalarBalanceBreakingBoundary
canonicalPostScalarBalanceBreakingBoundary =
  post-scalar-balance-breaking-boundary
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl
    "Assume the same-object target-centred scalar cancellation receipt is available. The next G2 payment is not another refinement of that same bound. Because the repository already owns the projective-balance strict-inequality no-go, the final route must exhibit an explicit balance defect, changed comparison object, strict off/cluster separation theorem, or genuinely different final margin on the exact literal consumer. Scalar closure plus such a same-object comparison-change receipt admits the final strict comparison stage; RH is not derived here."
