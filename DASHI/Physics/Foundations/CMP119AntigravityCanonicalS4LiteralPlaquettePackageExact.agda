{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4LiteralPlaquettePackageExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact as RowAState
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SameObjectPackageExact as S4
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109UVSameObjectExact as LiteralToSource
import DASHI.Physics.Foundations.CMP119AntigravityP3LiteralPlaquetteCMP109SameObjectExact as P3Literal
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CANONICAL S4 PACKAGE, WITH THE SOURCE-HISTORY WELD FACTORED THROUGH THE
-- LITERAL PLAQUETTE PRODUCER.
--
-- This is the preferred constructor whenever the CMP109 trajectory is already
-- attached to the literal localized plaquette running-coupling producer.
------------------------------------------------------------------------

record CanonicalS4LiteralPlaquetteInputs
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (inputs : BetaFlow.BetaDrivenCompleteDensityInputs {trajectory} {split})
    (rowA : RowA.FiniteQuarticResponseConstants)
    (smallFieldCap largeFieldCap covarianceCap : ℚ)
    (dataSet : Plaquette.PhysicalRunningCouplingData Agda.Builtin.Nat.Nat) : Set₂ where
  field
    betaCoordinates :
      RowAState.CanonicalRowABetaDrivenCoordinates
        inputs rowA smallFieldCap largeFieldCap covarianceCap

    bishopRunning :
      SU2.CanonicalBishopSU2RunningInputs Agda.Builtin.Nat.Nat

    p3RepresentsLiteralPlaquette :
      P3Literal.P3RepresentsLiteralPlaquetteUVView
        dataSet
        (SU2.recursion bishopRunning)

    literalPlaquetteRepresentsCMP109 :
      LiteralToSource.LiteralPlaquetteCMP109UVSameObject
        dataSet trajectory

    traceBoundary :
      SU2.CanonicalBishopSU2TraceBoundary

open CanonicalS4LiteralPlaquetteInputs public

asCanonicalS4SameObjectPackage :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap dataSet} →
  CanonicalS4LiteralPlaquetteInputs
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap dataSet →
  S4.CanonicalS4SameObjectPackage
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap
asCanonicalS4SameObjectPackage package = record
  { S4.CanonicalS4SameObjectPackage.betaCoordinates =
      betaCoordinates package
  ; S4.CanonicalS4SameObjectPackage.bishopRunning =
      bishopRunning package
  ; S4.CanonicalS4SameObjectPackage.bishopRunningRepresentsCMP109History =
      P3Literal.p3LiteralPlaquetteThenCMP109
        (p3RepresentsLiteralPlaquette package)
        (literalPlaquetteRepresentsCMP109 package)
  ; S4.CanonicalS4SameObjectPackage.traceBoundary =
      traceBoundary package
  }

directP3CMP109WitnessRequiredFromCanonicalCaller : Bool
directP3CMP109WitnessRequiredFromCanonicalCaller = false

p3LiteralPlaquetteIdentificationStillRequired : Bool
p3LiteralPlaquetteIdentificationStillRequired = true

literalPlaquetteCMP109IdentificationStillRequired : Bool
literalPlaquetteCMP109IdentificationStillRequired = true

directP3CMP109WitnessRequiredFromCanonicalCallerIsFalse :
  directP3CMP109WitnessRequiredFromCanonicalCaller ≡ false
directP3CMP109WitnessRequiredFromCanonicalCallerIsFalse = refl

canonicalS4LiteralPlaquettePackageCompilerLevel : ProofLevel
canonicalS4LiteralPlaquettePackageCompilerLevel = machineChecked

canonicalS4LiteralPlaquettePhysicalIdentificationLevel : ProofLevel
canonicalS4LiteralPlaquettePhysicalIdentificationLevel = conditional
