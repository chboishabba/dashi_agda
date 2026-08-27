module DASHI.Core.DecimalStageResidualBarrierExact where

------------------------------------------------------------------------
-- DECIMAL REFINEMENT / CANONICAL STAGE RESIDUAL BRIDGE
--
-- Mathematical background:
--
-- Stefan Banach,
-- "Sur les operations dans les ensembles abstraits et leur application aux
-- equations integrales", Fundamenta Mathematicae 3 (1922), 133--181.
-- Historical source for contraction/fixed-point iteration; no DOI asserted.
--
-- Donald E. Knuth,
-- "The Art of Computer Programming, Volume 2: Seminumerical Algorithms",
-- 3rd ed., Addison-Wesley, 1997. ISBN 9780201896848.
-- Standard positional/radix arithmetic background.
--
-- DASHI source/provenance:
--   supplied 2026-08-26/27 reconstruction of the +10% / repeated-digit
--   coarse/fine mechanism, cross-pollinated with the already-merged
--   StageValuationBundleAtlas from PR #347.
--
-- CLAIM BOUNDARY
--
-- DecimalResidualRefinementExact already owns the exact finite repeated-digit
-- numerators and the completed complement identity.  StageValuationBundleAtlas
-- already owns the canonical 0--11 stage carrier and guarded transitions.
-- This module introduces neither a new decimal calculus nor a new stage graph.
-- It proves only the finite bridge:
--
--   digit N < 9  -> a non-closed complement class remains;
--   digit 9      -> completed complement class is closed;
--   Stage 9 still has both an explicit self-loop and an explicit 9 -> 10 lift
--                    edge, so decimal refinement is not transition authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.DecimalResidualRefinementExact as Decimal
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Foundations.StageValuationBundleAtlas as Stage

------------------------------------------------------------------------
-- Exact digit-to-canonical-stage chart for the local 0..9 band.
------------------------------------------------------------------------

digitStage : Decimal.DecimalDigit → Atlas.StageAtlasZeroToEleven
digitStage Decimal.d0 = Atlas.atlas-0
digitStage Decimal.d1 = Atlas.atlas-1
digitStage Decimal.d2 = Atlas.atlas-2
digitStage Decimal.d3 = Atlas.atlas-3
digitStage Decimal.d4 = Atlas.atlas-4
digitStage Decimal.d5 = Atlas.atlas-5
digitStage Decimal.d6 = Atlas.atlas-6
digitStage Decimal.d7 = Atlas.atlas-7
digitStage Decimal.d8 = Atlas.atlas-8
digitStage Decimal.d9 = Atlas.atlas-9

stageIndexMatchesDigit :
  (digit : Decimal.DecimalDigit) →
  Atlas.toNat (digitStage digit) ≡ Decimal.digitValue digit
stageIndexMatchesDigit Decimal.d0 = refl
stageIndexMatchesDigit Decimal.d1 = refl
stageIndexMatchesDigit Decimal.d2 = refl
stageIndexMatchesDigit Decimal.d3 = refl
stageIndexMatchesDigit Decimal.d4 = refl
stageIndexMatchesDigit Decimal.d5 = refl
stageIndexMatchesDigit Decimal.d6 = refl
stageIndexMatchesDigit Decimal.d7 = refl
stageIndexMatchesDigit Decimal.d8 = refl
stageIndexMatchesDigit Decimal.d9 = refl

------------------------------------------------------------------------
-- "Stuck" as unresolved complement rather than lack of fine articulation.
------------------------------------------------------------------------

data CompletedResidualClass : Set where
  complementRemains completedComplementClosed : CompletedResidualClass

completedResidualClass : Decimal.DecimalDigit → CompletedResidualClass
completedResidualClass Decimal.d0 = complementRemains
completedResidualClass Decimal.d1 = complementRemains
completedResidualClass Decimal.d2 = complementRemains
completedResidualClass Decimal.d3 = complementRemains
completedResidualClass Decimal.d4 = complementRemains
completedResidualClass Decimal.d5 = complementRemains
completedResidualClass Decimal.d6 = complementRemains
completedResidualClass Decimal.d7 = complementRemains
completedResidualClass Decimal.d8 = complementRemains
completedResidualClass Decimal.d9 = completedComplementClosed

-- A carrier for the quantifier "every decimal digit below nine".  This avoids
-- smuggling an order theorem into what is fundamentally a finite exact chart.
data NonNineDigit : Set where
  n0 n1 n2 n3 n4 n5 n6 n7 n8 : NonNineDigit

asDigit : NonNineDigit → Decimal.DecimalDigit
asDigit n0 = Decimal.d0
asDigit n1 = Decimal.d1
asDigit n2 = Decimal.d2
asDigit n3 = Decimal.d3
asDigit n4 = Decimal.d4
asDigit n5 = Decimal.d5
asDigit n6 = Decimal.d6
asDigit n7 = Decimal.d7
asDigit n8 = Decimal.d8

allDigitsBelowNineRetainCompletedComplement :
  (digit : NonNineDigit) →
  completedResidualClass (asDigit digit) ≡ complementRemains
allDigitsBelowNineRetainCompletedComplement n0 = refl
allDigitsBelowNineRetainCompletedComplement n1 = refl
allDigitsBelowNineRetainCompletedComplement n2 = refl
allDigitsBelowNineRetainCompletedComplement n3 = refl
allDigitsBelowNineRetainCompletedComplement n4 = refl
allDigitsBelowNineRetainCompletedComplement n5 = refl
allDigitsBelowNineRetainCompletedComplement n6 = refl
allDigitsBelowNineRetainCompletedComplement n7 = refl
allDigitsBelowNineRetainCompletedComplement n8 = refl

nineAloneClosesCompletedComplement :
  completedResidualClass Decimal.d9 ≡ completedComplementClosed
nineAloneClosesCompletedComplement = refl

------------------------------------------------------------------------
-- Exact normalized-complement numerators over denominator nine.
------------------------------------------------------------------------

stage5CompletedGapNumeratorIsFour :
  Decimal.completedGapNumeratorOverNine Decimal.d5 ≡ 4
stage5CompletedGapNumeratorIsFour = refl

stage6CompletedGapNumeratorIsThree :
  Decimal.completedGapNumeratorOverNine Decimal.d6 ≡ 3
stage6CompletedGapNumeratorIsThree = refl

stage7CompletedGapNumeratorIsTwo :
  Decimal.completedGapNumeratorOverNine Decimal.d7 ≡ 2
stage7CompletedGapNumeratorIsTwo = refl

stage8CompletedGapNumeratorIsOne :
  Decimal.completedGapNumeratorOverNine Decimal.d8 ≡ 1
stage8CompletedGapNumeratorIsOne = refl

stage9CompletedGapNumeratorIsZero :
  Decimal.completedGapNumeratorOverNine Decimal.d9 ≡ 0
stage9CompletedGapNumeratorIsZero = refl

------------------------------------------------------------------------
-- Cross-pollination with the merged Stage-8 residual and Stage-9 barrier.
------------------------------------------------------------------------

canonicalStage8MissingAxisCountIsOne :
  Stage.Stage8ObstructionObservation.missingAxisCount
    Stage.canonicalStage8ObstructionObservation
  ≡ 1
canonicalStage8MissingAxisCountIsOne = refl

stage8DecimalComplementMatchesCanonicalMissingAxisCount :
  Decimal.completedGapNumeratorOverNine Decimal.d8
  ≡ Stage.Stage8ObstructionObservation.missingAxisCount
      Stage.canonicalStage8ObstructionObservation
stage8DecimalComplementMatchesCanonicalMissingAxisCount = refl

stage9HasCanonicalSelfLoop :
  Stage.GuardedStageEdge Atlas.atlas-9 Atlas.atlas-9
stage9HasCanonicalSelfLoop = Stage.systemicSelfLoop

stage9To10RequiresCanonicalExternalCoordinateEdge :
  Stage.GuardedStageEdge Atlas.atlas-9 Atlas.atlas-10
stage9To10RequiresCanonicalExternalCoordinateEdge =
  Stage.admitExternalCoordinate

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record DecimalStageResidualBarrierBoundary : Set where
  constructor decimal-stage-residual-barrier-boundary
  field
    decimalDepthAloneAuthorisesStageTransition : Bool
    decimalDepthAloneAuthorisesStageTransitionIsFalse :
      decimalDepthAloneAuthorisesStageTransition ≡ false
    decimalComplementDefinesPsychologicalState : Bool
    decimalComplementDefinesPsychologicalStateIsFalse :
      decimalComplementDefinesPsychologicalState ≡ false
    digitStageChartIsUniversalEmpiricalStageScale : Bool
    digitStageChartIsUniversalEmpiricalStageScaleIsFalse :
      digitStageChartIsUniversalEmpiricalStageScale ≡ false
    stage8DecimalOneIsClaimedAsCauseOfEveryStage8Residual : Bool
    stage8DecimalOneIsClaimedAsCauseOfEveryStage8ResidualIsFalse :
      stage8DecimalOneIsClaimedAsCauseOfEveryStage8Residual ≡ false

canonicalDecimalStageResidualBarrierBoundary :
  DecimalStageResidualBarrierBoundary
canonicalDecimalStageResidualBarrierBoundary =
  decimal-stage-residual-barrier-boundary
    false refl
    false refl
    false refl
    false refl
