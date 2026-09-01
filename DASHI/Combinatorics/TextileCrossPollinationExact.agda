module DASHI.Combinatorics.TextileCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.List using (length)

import DASHI.Combinatorics.TextileNFibreCalculusExact as T
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Admissible

------------------------------------------------------------------------
-- Cross-pollination owner for the n-fibre textile kernel.
--
-- This imports proof SHAPES, not domain semantics, from the wider repository:
--   * proof-relevant enabled transitions;
--   * coarse observation versus retained process history;
--   * path/rewrite equivalence distinct from literal word identity;
--   * flat versus periodic/cyclic carrier boundary conditions;
--   * common event skeletons without collapsing craft-specific grammars.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Literal braid word equality != braid-rewrite equivalence.
--
-- The existing three-fibre words are distinct histories.  We retain that
-- distinction while separately admitting the elementary Yang--Baxter rewrite
-- as a process-equivalence witness.
------------------------------------------------------------------------

data BraidRewrite3 : T.BraidWord 3 → T.BraidWord 3 → Set where
  yangBaxterRewrite :
    BraidRewrite3
      T.threeFibreYangBaxterLeft
      T.threeFibreYangBaxterRight

data BraidEquivalent3 : T.BraidWord 3 → T.BraidWord 3 → Set where
  braidEqRefl :
    {w : T.BraidWord 3} →
    BraidEquivalent3 w w

  braidEqStep :
    {u v : T.BraidWord 3} →
    BraidRewrite3 u v →
    BraidEquivalent3 u v

  braidEqSym :
    {u v : T.BraidWord 3} →
    BraidEquivalent3 u v →
    BraidEquivalent3 v u

  braidEqTrans :
    {u v w : T.BraidWord 3} →
    BraidEquivalent3 u v →
    BraidEquivalent3 v w →
    BraidEquivalent3 u w

threeFibreYangBaxterEquivalent :
  BraidEquivalent3
    T.threeFibreYangBaxterLeft
    T.threeFibreYangBaxterRight
threeFibreYangBaxterEquivalent =
  braidEqStep yangBaxterRewrite

------------------------------------------------------------------------
-- 2. Coarse visible pattern != retained crossing history.
--
-- Both Yang--Baxter words contain three crossings.  A coarse observation that
-- keeps only fibre count and crossing count therefore collapses them even
-- though the repository retains distinct word histories.
------------------------------------------------------------------------

record CoarseBraidSurface : Set where
  constructor coarseBraidSurface
  field
    fibreCount : Nat
    crossingCount : Nat

open CoarseBraidSurface public

observeThreeBraid : T.BraidWord 3 → CoarseBraidSurface
observeThreeBraid w = coarseBraidSurface 3 (length w)

threeYangBaxterWordsShareCoarseSurface :
  observeThreeBraid T.threeFibreYangBaxterLeft
  ≡
  observeThreeBraid T.threeFibreYangBaxterRight
threeYangBaxterWordsShareCoarseSurface = refl

------------------------------------------------------------------------
-- 3. Flat versus cyclic textile topology.
--
-- Inspired by the repository's strict distinction between a periodic carrier
-- and a cut/non-periodic carrier.  Same local stitch vocabulary and loop count
-- do not identify flat knitting with knitting in the round.
------------------------------------------------------------------------

data TextileBoundaryCondition : Set where
  flatBoundary : TextileBoundaryCondition
  cyclicBoundary : TextileBoundaryCondition

record KnitCarrierTopology : Set where
  constructor knitCarrierTopology
  field
    liveLoopCount : Nat
    boundaryCondition : TextileBoundaryCondition
    localOperations : List T.KnitLoopOp

open KnitCarrierTopology public

flatThreeLoopCarrier : KnitCarrierTopology
flatThreeLoopCarrier =
  knitCarrierTopology
    3
    flatBoundary
    (T.knitThrough 0 ∷ T.knitThrough 1 ∷ T.knitThrough 2 ∷ [])

cyclicThreeLoopCarrier : KnitCarrierTopology
cyclicThreeLoopCarrier =
  knitCarrierTopology
    3
    cyclicBoundary
    (T.knitThrough 0 ∷ T.knitThrough 1 ∷ T.knitThrough 2 ∷ [])

sameLocalLoopCount :
  liveLoopCount flatThreeLoopCarrier
  ≡
  liveLoopCount cyclicThreeLoopCarrier
sameLocalLoopCount = refl

sameLocalOperationCount :
  length (localOperations flatThreeLoopCarrier)
  ≡
  length (localOperations cyclicThreeLoopCarrier)
sameLocalOperationCount = refl

flatAndCyclicBoundariesDiffer :
  ¬ (boundaryCondition flatThreeLoopCarrier
     ≡ boundaryCondition cyclicThreeLoopCarrier)
flatAndCyclicBoundariesDiffer ()

------------------------------------------------------------------------
-- 4. Common event skeleton without craft collapse.
--
-- Braiding, weaving, knitting and crochet can all be projected to a common
-- low-level passage/loop event language, but the projection deliberately loses
-- craft-specific dependency and carrier structure.
------------------------------------------------------------------------

data CommonTextileEvent : Set where
  adjacentPass : Nat → T.CrossingOrientation → CommonTextileEvent
  warpWeftPass : Nat → Nat → T.CrossingOrientation → CommonTextileEvent
  priorLoopPass : Nat → CommonTextileEvent
  hookInsertion : Nat → CommonTextileEvent
  activeLoopPull : CommonTextileEvent

braidEvent : {n : Nat} → T.AdjacentCrossing n → CommonTextileEvent
braidEvent c = adjacentPass (T.leftIndex c) (T.orientation c)

weaveEvent : T.WeavePass → CommonTextileEvent
weaveEvent (T.warpOverWeft i j) = warpWeftPass i j T.overCrossing
weaveEvent (T.warpUnderWeft i j) = warpWeftPass i j T.underCrossing

knitEvent : T.KnitLoopOp → CommonTextileEvent
knitEvent (T.knitThrough i) = priorLoopPass i
knitEvent (T.purlThrough i) = priorLoopPass i
knitEvent (T.passSlip i) = priorLoopPass i
knitEvent (T.knitTogether i j) = priorLoopPass i

crochetEvent : T.CrochetHookOp → CommonTextileEvent
crochetEvent T.yarnOver = activeLoopPull
crochetEvent T.pullThroughActive = activeLoopPull
crochetEvent (T.insertInto i) = hookInsertion i
crochetEvent T.pullThroughTwo = activeLoopPull
crochetEvent T.chainOne = activeLoopPull

------------------------------------------------------------------------
-- 5. Craft-specific dependency grammar.
------------------------------------------------------------------------

data DependencyKind : Set where
  permutationDependency : DependencyKind
  twoFamilyInterlacementDependency : DependencyKind
  retainedLoopDependency : DependencyKind
  distinguishedActiveLoopDependency : DependencyKind

craftDependency : T.TextileKind → DependencyKind
craftDependency T.braidKind = permutationDependency
craftDependency T.plaitKind = permutationDependency
craftDependency T.weaveKind = twoFamilyInterlacementDependency
craftDependency T.knitKind = retainedLoopDependency
craftDependency T.crochetKind = distinguishedActiveLoopDependency

------------------------------------------------------------------------
-- 6. Proof-relevant move admissibility.
--
-- A textile move is first enabled or disabled on the current carrier; it is
-- not merely assigned a small weight/probability.  This is a literal instance
-- of the generic admissible-transition hyperfabric from merged PR #647.
------------------------------------------------------------------------

data TextileIntegrity : Set where
  intactCarrier : TextileIntegrity
  damagedCarrier : TextileIntegrity

data TextileMove : Set where
  makeAdjacentCrossing : TextileMove

data TextileParameter : Set where
  ordinaryWorkingTension : TextileParameter

data TextileEnabled : TextileMove → TextileParameter → TextileIntegrity → Set where
  crossingEnabledOnIntact :
    TextileEnabled
      makeAdjacentCrossing
      ordinaryWorkingTension
      intactCarrier

textileStep : TextileMove → TextileParameter → TextileIntegrity → TextileIntegrity
textileStep makeAdjacentCrossing ordinaryWorkingTension intactCarrier = intactCarrier
textileStep makeAdjacentCrossing ordinaryWorkingTension damagedCarrier = damagedCarrier

data TextileInvariant : TextileIntegrity → Set where
  intactInvariant : TextileInvariant intactCarrier

textilePreservesInvariant :
  (move : TextileMove) →
  (parameter : TextileParameter) →
  (state : TextileIntegrity) →
  TextileEnabled move parameter state →
  TextileInvariant state →
  TextileInvariant (textileStep move parameter state)
textilePreservesInvariant
  makeAdjacentCrossing ordinaryWorkingTension intactCarrier
  crossingEnabledOnIntact intactInvariant =
  intactInvariant

textileTransitionSystem : Admissible.AdmissibleTransitionSystem
textileTransitionSystem =
  Admissible.admissibleTransitionSystem
    TextileIntegrity
    TextileParameter
    TextileMove
    TextileEnabled
    textileStep
    TextileInvariant
    textilePreservesInvariant
    "Textile crossing admissibility is proof-relevant before weighting"

damagedCarrierDisablesCrossing :
  TextileEnabled
    makeAdjacentCrossing
    ordinaryWorkingTension
    damagedCarrier
  → ⊥
damagedCarrierDisablesCrossing ()

noAdmittedCrossingOnDamagedCarrier :
  Admissible.AdmittedStep
    textileTransitionSystem
    makeAdjacentCrossing
    ordinaryWorkingTension
    damagedCarrier
  → ⊥
noAdmittedCrossingOnDamagedCarrier =
  Admissible.disabledExcludesAdmittedStep
    damagedCarrierDisablesCrossing

canonicalAdmittedCrossing :
  Admissible.AdmittedStep
    textileTransitionSystem
    makeAdjacentCrossing
    ordinaryWorkingTension
    intactCarrier
canonicalAdmittedCrossing =
  Admissible.admittedStep crossingEnabledOnIntact intactInvariant

------------------------------------------------------------------------
-- 7. nMin >= 15 remains a floor, while the calculus stays unbounded.
------------------------------------------------------------------------

crossPollinatedNMin : Nat
crossPollinatedNMin = T.nMinFibreTarget

crossPollinatedNMinIsFifteen : crossPollinatedNMin ≡ 15
crossPollinatedNMinIsFifteen = refl

fifteenFibreSweepStillPresent :
  T.braidSteps T.braid15 ≡ T.allAdjacentCrossings 13
fifteenFibreSweepStillPresent = T.braid15IsFullAdjacentSweep

------------------------------------------------------------------------
-- Boundary: shared skeleton, shared counts or rewrite equivalence do not
-- collapse the five textile crafts or erase the retained fine history.
------------------------------------------------------------------------

record TextileCrossPollinationBoundary : Set where
  constructor textileCrossPollinationBoundary
  field
    commonEventSkeletonImpliesSameCraft : Bool
    commonEventSkeletonImpliesSameCraftIsFalse :
      commonEventSkeletonImpliesSameCraft ≡ false

    sameCoarsePatternImpliesSameHistory : Bool
    sameCoarsePatternImpliesSameHistoryIsFalse :
      sameCoarsePatternImpliesSameHistory ≡ false

    rewriteEquivalentMeansLiteralWordEquality : Bool
    rewriteEquivalentMeansLiteralWordEqualityIsFalse :
      rewriteEquivalentMeansLiteralWordEquality ≡ false

    sameLocalStitchesIdentifyFlatAndCyclicCarrier : Bool
    sameLocalStitchesIdentifyFlatAndCyclicCarrierIsFalse :
      sameLocalStitchesIdentifyFlatAndCyclicCarrier ≡ false

    disabledMoveIsMerelyLowProbability : Bool
    disabledMoveIsMerelyLowProbabilityIsFalse :
      disabledMoveIsMerelyLowProbability ≡ false

open TextileCrossPollinationBoundary public

canonicalTextileCrossPollinationBoundary : TextileCrossPollinationBoundary
canonicalTextileCrossPollinationBoundary =
  textileCrossPollinationBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
