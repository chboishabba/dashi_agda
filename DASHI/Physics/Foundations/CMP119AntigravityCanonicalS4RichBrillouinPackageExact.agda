{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4RichBrillouinPackageExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact as RowAState
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SameObjectPackageExact as S4
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109UVSameObjectExact as LiteralToSource
import DASHI.Physics.Foundations.CMP119AntigravityP3LiteralPlaquetteCMP109SameObjectExact as P3Literal
import DASHI.Physics.Foundations.CMP119AntigravityP3RichBrillouinLiteralPlaquetteExact as RichBridge
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CANONICAL S4 PACKAGE THROUGH THE RICH T4 BRILLOUIN GAUSSIAN CARRIER
--
-- This removes the normalized-log-coordinate theorem from the preferred S4
-- caller.  The canonical Bishop convention and the literal CMP109 history are
-- connected through the same P3 Gaussian field and the physical rich shell
-- integral.
------------------------------------------------------------------------

record CanonicalS4RichBrillouinInputs
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (inputs : BetaFlow.BetaDrivenCompleteDensityInputs {trajectory} {split})
    (rowA : RowA.FiniteQuarticResponseConstants)
    (smallFieldCap largeFieldCap covarianceCap : ℚ)
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ) : Set₂ where
  field
    betaCoordinates :
      RowAState.CanonicalRowABetaDrivenCoordinates
        inputs rowA smallFieldCap largeFieldCap covarianceCap

    bishopRunning :
      SU2.CanonicalBishopSU2RunningInputs Nat

    p3RichBrillouinLiteralBridge :
      RichBridge.P3RepresentsRichBrillouinLiteralPlaquetteSplit
        dataSet rich
        (SU2.recursion bishopRunning)

    literalPlaquetteRepresentsCMP109 :
      LiteralToSource.LiteralPlaquetteCMP109UVSameObject
        dataSet trajectory

    traceBoundary :
      SU2.CanonicalBishopSU2TraceBoundary

open CanonicalS4RichBrillouinInputs public

asCanonicalS4SameObjectPackage :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap
      dataSet rich} →
  CanonicalS4RichBrillouinInputs
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap dataSet rich →
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
        (RichBridge.richBrillouinViewAsLiteralTotal
          (p3RichBrillouinLiteralBridge package))
        (literalPlaquetteRepresentsCMP109 package)
  ; S4.CanonicalS4SameObjectPackage.traceBoundary =
      traceBoundary package
  }

normalizedLiteralLogCoordinateRequiredFromCanonicalCaller : Bool
normalizedLiteralLogCoordinateRequiredFromCanonicalCaller = false

directP3LiteralGaussianWitnessRequiredFromCanonicalCaller : Bool
directP3LiteralGaussianWitnessRequiredFromCanonicalCaller = false

directP3CMP109WitnessRequiredFromCanonicalCaller : Bool
directP3CMP109WitnessRequiredFromCanonicalCaller = false

richGaussianSameObjectWitnessRequiredFromCanonicalCaller : Bool
richGaussianSameObjectWitnessRequiredFromCanonicalCaller = true

normalizedLiteralLogCoordinateRequiredFromCanonicalCallerIsFalse :
  normalizedLiteralLogCoordinateRequiredFromCanonicalCaller ≡ false
normalizedLiteralLogCoordinateRequiredFromCanonicalCallerIsFalse = refl

directP3LiteralGaussianWitnessRequiredFromCanonicalCallerIsFalse :
  directP3LiteralGaussianWitnessRequiredFromCanonicalCaller ≡ false
directP3LiteralGaussianWitnessRequiredFromCanonicalCallerIsFalse = refl

directP3CMP109WitnessRequiredFromCanonicalCallerIsFalse :
  directP3CMP109WitnessRequiredFromCanonicalCaller ≡ false
directP3CMP109WitnessRequiredFromCanonicalCallerIsFalse = refl

canonicalS4RichBrillouinPackageCompilerLevel : ProofLevel
canonicalS4RichBrillouinPackageCompilerLevel = machineChecked

canonicalS4RichBrillouinPhysicalSameObjectLevel : ProofLevel
canonicalS4RichBrillouinPhysicalSameObjectLevel = conditional
