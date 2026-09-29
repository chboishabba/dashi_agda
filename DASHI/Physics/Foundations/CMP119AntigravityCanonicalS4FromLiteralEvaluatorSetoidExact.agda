{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4FromLiteralEvaluatorSetoidExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact as RowAState
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SetoidPhysicalPackageExact as S4
import DASHI.Physics.Foundations.CMP119AntigravityLiteralEvaluatorFiniteModeSameObjectExact as Evaluator
import DASHI.Physics.Foundations.CMP119AntigravityP3GFromLiteralEvaluatorFiniteModeExact as FromEvaluator
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteMode
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

------------------------------------------------------------------------
-- Preferred S4 producer from the *one* evaluator source: the CMP109 weld
-- and rich projection are generated from its common finite-mode source.
------------------------------------------------------------------------

record CanonicalS4LiteralEvaluatorSource
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
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ)
    (running : SU2.CanonicalBishopSU2RunningInputs Nat) : Set₂ where
  field
    betaCoordinates :
      RowAState.CanonicalRowABetaDrivenCoordinates
        inputs rowA smallFieldCap largeFieldCap covarianceCap

    evaluatorSameObject :
      Evaluator.LiteralEvaluatorFiniteModeSameObject
        {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
        {expressions = expressions} {ward = ward} {scalarData = scalarData}
        finiteMode oneLoop remainder rich running

    traceBoundary :
      SU2.CanonicalBishopSU2TraceBoundary

open CanonicalS4LiteralEvaluatorSource public

asCanonicalSetoidS4 :
  ∀ {trajectory split Mode Atom expressions ward scalarData
       inputs rowA smallFieldCap largeFieldCap covarianceCap
       finiteMode oneLoop remainder rich running} →
  CanonicalS4LiteralEvaluatorSource
    {trajectory = trajectory} {split = split}
    {Mode = Mode} {Atom = Atom}
    {expressions = expressions} {ward = ward} {scalarData = scalarData}
    inputs rowA smallFieldCap largeFieldCap covarianceCap
    finiteMode oneLoop remainder rich running →
  S4.CanonicalS4SetoidPhysicalPackage
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap
asCanonicalSetoidS4 {rich = rich} source = record
  { S4.CanonicalS4SetoidPhysicalPackage.betaCoordinates =
      betaCoordinates source
  ; S4.CanonicalS4SetoidPhysicalPackage.coefficientWeld =
      FromEvaluator.coefficientWeld (evaluatorSameObject source)
  ; S4.CanonicalS4SetoidPhysicalPackage.rich = rich
  ; S4.CanonicalS4SetoidPhysicalPackage.geometry =
      FromEvaluator.asP3GSetoidPhysicalGeometry
        (evaluatorSameObject source)
  ; S4.CanonicalS4SetoidPhysicalPackage.traceBoundary =
      traceBoundary source
  }
