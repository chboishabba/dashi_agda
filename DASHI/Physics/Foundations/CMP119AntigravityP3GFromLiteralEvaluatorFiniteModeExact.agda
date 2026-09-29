{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3GFromLiteralEvaluatorFiniteModeExact where

open import Agda.Builtin.Nat using (Nat)
import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityFiniteModePlaquetteBetaSameObjectExact as FinitePlaquette
import DASHI.Physics.Foundations.CMP119AntigravityLiteralEvaluatorFiniteModeSameObjectExact as Evaluator
import DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidPhysicalCoreExact as Core
import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinFiniteModeGaussianProjectionExact as Gaussian
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as Running
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteMode
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

-- One evaluator/finite-mode object owns both P3G physical-source witnesses.

coefficientWeld :
  ∀ {trajectory Mode Atom expressions ward scalarData}
    {finiteMode : FiniteMode.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {oneLoop : Plaquette.OneLoopVacuumPolarizationData Nat}
    {remainder : Plaquette.PlaquetteRemainderData Nat}
    {rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ}
    {running : Running.CanonicalBishopSU2RunningInputs Nat} →
  Evaluator.LiteralEvaluatorFiniteModeSameObject
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {expressions = expressions} {ward = ward} {scalarData = scalarData}
    finiteMode oneLoop remainder rich running →
  Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory
coefficientWeld source =
  FinitePlaquette.asCMP109LiteralPlaquetteCoefficientWeld
    (Evaluator.finiteModePlaquette source)

asP3GSetoidPhysicalGeometry :
  ∀ {trajectory Mode Atom expressions ward scalarData}
    {finiteMode : FiniteMode.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {oneLoop : Plaquette.OneLoopVacuumPolarizationData Nat}
    {remainder : Plaquette.PlaquetteRemainderData Nat}
    {rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ}
    {running : Running.CanonicalBishopSU2RunningInputs Nat}
    (source :
      Evaluator.LiteralEvaluatorFiniteModeSameObject
        {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
        {expressions = expressions} {ward = ward} {scalarData = scalarData}
        finiteMode oneLoop remainder rich running) →
  Core.P3GSetoidPhysicalGeometry (coefficientWeld source) rich
asP3GSetoidPhysicalGeometry source = record
  { Core.P3GSetoidPhysicalGeometry.richAddIsBishopAdd =
      Evaluator.richAddIsBishopAdd source
  ; Core.P3GSetoidPhysicalGeometry.gaussianProjection =
      Gaussian.asRichBrillouinRationalGaussianProjection
        (Evaluator.asRichBrillouinFiniteModeGaussianSameObject source)
  }
