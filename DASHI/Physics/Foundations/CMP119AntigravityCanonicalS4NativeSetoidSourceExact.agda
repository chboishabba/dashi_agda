{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4NativeSetoidSourceExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact as RowAState
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SetoidPhysicalPackageExact as S4
import DASHI.Physics.Foundations.CMP119AntigravityP3GNativeSetoidLiteralEvaluatorExact as Native
import DASHI.Physics.Foundations.CMP119AntigravityFiniteModePlaquetteBetaSameObjectExact as FinitePlaquette
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteMode
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

------------------------------------------------------------------------
-- Canonical S4 physical source: no legacy P3 record anywhere in its contract.
-- The old running convention is not invoked by this entrypoint.
------------------------------------------------------------------------

record CanonicalS4NativeSetoidSource
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    {Mode Atom expressions ward scalarData : Set}
    (inputs : BetaFlow.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split})
    (rowA : RowA.FiniteQuarticResponseConstants)
    (smallFieldCap largeFieldCap covarianceCap : ℚ)
    (finiteMode : FiniteMode.FiniteModeBetaTrajectoryData trajectory Mode Atom)
    (oneLoop : Plaquette.OneLoopVacuumPolarizationData Nat)
    (remainder : Plaquette.PlaquetteRemainderData Nat)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ) : Set₂ where
  field
    betaCoordinates :
      RowAState.CanonicalRowABetaDrivenCoordinates
        inputs rowA smallFieldCap largeFieldCap covarianceCap

    literalEvaluator :
      Native.NativeSetoidLiteralEvaluatorSource
        {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
        {expressions = expressions} {ward = ward} {scalarData = scalarData}
        finiteMode oneLoop remainder rich

    traceBoundary :
      SU2.CanonicalBishopSU2TraceBoundary

open CanonicalS4NativeSetoidSource public

asPhysicalS4 :
  ∀ {trajectory split Mode Atom expressions ward scalarData
       inputs rowA smallFieldCap largeFieldCap covarianceCap
       finiteMode oneLoop remainder rich}
    (source : CanonicalS4NativeSetoidSource
      {trajectory = trajectory} {split = split}
      {Mode = Mode} {Atom = Atom}
      {expressions = expressions} {ward = ward} {scalarData = scalarData}
      inputs rowA smallFieldCap largeFieldCap covarianceCap
      finiteMode oneLoop remainder rich) →
  S4.CanonicalS4SetoidPhysicalPackage
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap
asPhysicalS4 {rich = rich} source = record
  { S4.CanonicalS4SetoidPhysicalPackage.betaCoordinates =
      betaCoordinates source
  ; S4.CanonicalS4SetoidPhysicalPackage.coefficientWeld =
      FinitePlaquette.asCMP109LiteralPlaquetteCoefficientWeld
        (Native.finiteModePlaquette (literalEvaluator source))
  ; S4.CanonicalS4SetoidPhysicalPackage.rich = rich
  ; S4.CanonicalS4SetoidPhysicalPackage.geometry =
      Native.asPhysicalGeometry (literalEvaluator source)
  ; S4.CanonicalS4SetoidPhysicalPackage.traceBoundary =
      traceBoundary source
  }
