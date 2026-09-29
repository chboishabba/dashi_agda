{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4StateOnlySameObjectExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact as RowAState
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SameObjectPackageExact as S4
import DASHI.Physics.Foundations.CMP119AntigravityP3StateForcesSourceIncrementExact as State
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- MINIMAL CANONICAL S4 SAME-OBJECT CUT
--
-- P3's exact recursion already determines its total increment once:
--
--   * its inverse-coupling state is the CMP109 UV state,
--   * its nextScale is the source predecessor, and
--   * its addition is Bishop addition.
--
-- Therefore S4 does not need an independent beta/remainder split, literal
-- plaquette weld, Brillouin projection, finite-mode epsilon, or normalized
-- log coordinate in order to identify the running history.
------------------------------------------------------------------------

record CanonicalS4StateOnlyInputs
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

    p3StateRepresentsSourceUV :
      State.P3StateRepresentsSourceUV
        trajectory
        (SU2.recursion bishopRunning)

    traceBoundary : SU2.CanonicalBishopSU2TraceBoundary

open CanonicalS4StateOnlyInputs public

asCanonicalS4SameObjectPackage :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap} →
  CanonicalS4StateOnlyInputs
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
        (p3StateRepresentsSourceUV package)
  ; S4.CanonicalS4SameObjectPackage.traceBoundary = traceBoundary package
  }

independentP3TotalIncrementWitnessRequired : Bool
independentP3TotalIncrementWitnessRequired = false

independentP3RemainderWitnessRequired : Bool
independentP3RemainderWitnessRequired = false

literalPlaquetteWeldRequiredForS4History : Bool
literalPlaquetteWeldRequiredForS4History = false

richBrillouinProjectionRequiredForS4History : Bool
richBrillouinProjectionRequiredForS4History = false

finiteModeGaussianRequiredForS4History : Bool
finiteModeGaussianRequiredForS4History = false

p3StateSameObjectStillRequired : Bool
p3StateSameObjectStillRequired = true

independentP3TotalIncrementWitnessRequiredIsFalse :
  independentP3TotalIncrementWitnessRequired ≡ false
independentP3TotalIncrementWitnessRequiredIsFalse = refl

independentP3RemainderWitnessRequiredIsFalse :
  independentP3RemainderWitnessRequired ≡ false
independentP3RemainderWitnessRequiredIsFalse = refl

literalPlaquetteWeldRequiredForS4HistoryIsFalse :
  literalPlaquetteWeldRequiredForS4History ≡ false
literalPlaquetteWeldRequiredForS4HistoryIsFalse = refl

richBrillouinProjectionRequiredForS4HistoryIsFalse :
  richBrillouinProjectionRequiredForS4History ≡ false
richBrillouinProjectionRequiredForS4HistoryIsFalse = refl

finiteModeGaussianRequiredForS4HistoryIsFalse :
  finiteModeGaussianRequiredForS4History ≡ false
finiteModeGaussianRequiredForS4HistoryIsFalse = refl

p3StateSameObjectStillRequiredIsTrue :
  p3StateSameObjectStillRequired ≡ true
p3StateSameObjectStillRequiredIsTrue = refl

canonicalS4StateOnlyCompilerLevel : ProofLevel
canonicalS4StateOnlyCompilerLevel = machineChecked

p3StateSourceSameObjectIdentificationLevel : ProofLevel
p3StateSourceSameObjectIdentificationLevel = conditional
