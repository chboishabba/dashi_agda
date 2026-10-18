{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4LiteralRecurrenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact as RowAState
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SameObjectPackageExact as S4
import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityP3LiteralPlaquetteRecurrenceSameObjectExact as Local
import DASHI.Physics.Foundations.CMP119AntigravityP3SourceRecurrenceUniquenessExact as Recurrence
import DASHI.Physics.Foundations.CMP119AntigravityP3StateForcesSourceIncrementExact as State
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CANONICAL S4 THROUGH THE LOCAL LITERAL RECURRENCE CUT
--
-- The literal plaquette producer is already welded to CMP109 by the preferred
-- coefficient constructor.  Therefore S4 only needs local P3/literal data:
--
--   one depth-zero state anchor
--   + source predecessor map
--   + literal total increment on each positive edge
--   + Bishop addition.
--
-- Zero increment and every all-depth state equality are compiler consequences.
------------------------------------------------------------------------

record CanonicalS4LiteralRecurrenceInputs
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

    coefficientWeld :
      Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory

    localP3LiteralRecurrence :
      Local.P3LiteralPlaquetteRecurrenceSameObject
        (Constructor.asPhysicalRunningCouplingData coefficientWeld)
        (SU2.recursion bishopRunning)

    traceBoundary : SU2.CanonicalBishopSU2TraceBoundary

open CanonicalS4LiteralRecurrenceInputs public

sourceRecurrenceSameObject :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap}
    (package : CanonicalS4LiteralRecurrenceInputs
      {trajectory = trajectory} {split = split}
      inputs rowA smallFieldCap largeFieldCap covarianceCap) →
  Recurrence.P3SourceRecurrenceSameObject
    trajectory
    (SU2.recursion (bishopRunning package))
sourceRecurrenceSameObject package =
  Local.asSourceRecurrenceSameObject
    (localP3LiteralRecurrence package)
    (Constructor.asLiteralPlaquetteCMP109UVSameObject
      (coefficientWeld package))

asCanonicalS4SameObjectPackage :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap} →
  CanonicalS4LiteralRecurrenceInputs
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap →
  S4.CanonicalS4SameObjectPackage
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap
asCanonicalS4SameObjectPackage package = record
  { S4.CanonicalS4SameObjectPackage.betaCoordinates = betaCoordinates package
  ; S4.CanonicalS4SameObjectPackage.bishopRunning = bishopRunning package
  ; S4.CanonicalS4SameObjectPackage.bishopRunningRepresentsCMP109History =
      State.asP3RepresentsSourceUVView
        (Recurrence.asP3StateRepresentsSourceUV
          (sourceRecurrenceSameObject package))
  ; S4.CanonicalS4SameObjectPackage.traceBoundary = traceBoundary package
  }

allDepthP3StateWitnessRequired : Bool
allDepthP3StateWitnessRequired = false

zeroIncrementWitnessRequired : Bool
zeroIncrementWitnessRequired = false

onlyInitialStateAnchorRequired : Bool
onlyInitialStateAnchorRequired = true

positiveEdgeLiteralIncrementIdentificationRequired : Bool
positiveEdgeLiteralIncrementIdentificationRequired = true

allDepthP3StateWitnessRequiredIsFalse :
  allDepthP3StateWitnessRequired ≡ false
allDepthP3StateWitnessRequiredIsFalse = refl

zeroIncrementWitnessRequiredIsFalse :
  zeroIncrementWitnessRequired ≡ false
zeroIncrementWitnessRequiredIsFalse = refl

canonicalS4LiteralRecurrenceCompilerLevel : ProofLevel
canonicalS4LiteralRecurrenceCompilerLevel = machineChecked
