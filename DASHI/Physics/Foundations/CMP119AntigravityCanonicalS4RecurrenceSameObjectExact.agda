{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4RecurrenceSameObjectExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact as RowAState
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SameObjectPackageExact as S4
import DASHI.Physics.Foundations.CMP119AntigravityP3SourceRecurrenceUniquenessExact as Recurrence
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CANONICAL S4 VIA LOCAL RECURRENCE SAME-OBJECT DATA
--
-- Replace the all-depth state weld by the strictly smaller local package:
--
--   same UV anchor
--   + same predecessor map
--   + same total increment on every source edge
--   + Bishop addition.
--
-- Recurrence uniqueness then constructs the all-depth P3/CMP109 state weld.
------------------------------------------------------------------------

record CanonicalS4RecurrenceInputs
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (inputs : BetaFlow.BetaDrivenCompleteDensityInputs {trajectory} {split})
    (rowA : RowA.FiniteQuarticResponseConstants)
    (smallFieldCap largeFieldCap covarianceCap : ℚ) : Set₂ where
  field
    betaCoordinates :
      RowAState.CanonicalRowABetaDrivenCoordinates
        inputs rowA smallFieldCap largeFieldCap covarianceCap

    bishopRunning : SU2.CanonicalBishopSU2RunningInputs Nat

    recurrenceSameObject :
      Recurrence.P3SourceRecurrenceSameObject
        trajectory
        (SU2.recursion bishopRunning)

    traceBoundary : SU2.CanonicalBishopSU2TraceBoundary

open CanonicalS4RecurrenceInputs public

asCanonicalS4SameObjectPackage :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap} →
  CanonicalS4RecurrenceInputs
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap →
  S4.CanonicalS4SameObjectPackage
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap
asCanonicalS4SameObjectPackage package = record
  { S4.CanonicalS4SameObjectPackage.betaCoordinates = betaCoordinates package
  ; S4.CanonicalS4SameObjectPackage.bishopRunning = bishopRunning package
  ; S4.CanonicalS4SameObjectPackage.bishopRunningRepresentsCMP109History =
      DASHI.Physics.Foundations.CMP119AntigravityP3StateForcesSourceIncrementExact.asP3RepresentsSourceUVView
        (Recurrence.asP3StateRepresentsSourceUV
          (recurrenceSameObject package))
  ; S4.CanonicalS4SameObjectPackage.traceBoundary = traceBoundary package
  }

allDepthP3StateWitnessRequired : Bool
allDepthP3StateWitnessRequired = false

sameUVAnchorStillRequired : Bool
sameUVAnchorStillRequired = true

sameOneStepIncrementStillRequired : Bool
sameOneStepIncrementStillRequired = true

allDepthP3StateWitnessRequiredIsFalse :
  allDepthP3StateWitnessRequired ≡ false
allDepthP3StateWitnessRequiredIsFalse = refl

sameUVAnchorStillRequiredIsTrue :
  sameUVAnchorStillRequired ≡ true
sameUVAnchorStillRequiredIsTrue = refl

sameOneStepIncrementStillRequiredIsTrue :
  sameOneStepIncrementStillRequired ≡ true
sameOneStepIncrementStillRequiredIsTrue = refl

canonicalS4RecurrenceSameObjectCompilerLevel : ProofLevel
canonicalS4RecurrenceSameObjectCompilerLevel = machineChecked
