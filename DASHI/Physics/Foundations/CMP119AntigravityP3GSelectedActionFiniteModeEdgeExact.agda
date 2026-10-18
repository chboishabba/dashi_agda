{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3GSelectedActionFiniteModeEdgeExact where

open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (cong)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityP3GFromLiteralEvaluatorFiniteModeExact as EvaluatorBridge
import DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidPhysicalCoreExact as Core
import DASHI.Physics.Foundations.CMP119AntigravityLiteralEvaluatorFiniteModeSameObjectExact as Evaluator
import DASHI.Physics.Foundations.CMP119AntigravitySelectedActionFiniteModePhysicalWeldExact as Action
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as Running
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteMode
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

-- No independent beta=selected-action equality:
-- selected-action coefficient and physical P3G increment meet through the
-- SAME finite-mode source and its five termwise projector identifications.

positiveEdgeP3GIsSelectedAction :
  ∀ {trajectory Mode Atom expressions ward scalarData}
    {finiteMode : FiniteMode.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {oneLoop : Plaquette.OneLoopVacuumPolarizationData Nat}
    {remainder : Plaquette.PlaquetteRemainderData Nat}
    {rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ}
    {running : Running.CanonicalBishopSU2RunningInputs Nat}
    {selectedAction : Plaquette.ExactOneStepEffectiveActionData Nat}
    (actionWeld :
      Action.SelectedActionFiniteModePlaquetteIdentification
        finiteMode oneLoop remainder selectedAction)
    (evaluator :
      Evaluator.LiteralEvaluatorFiniteModeSameObject
        {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
        {expressions = expressions} {ward = ward} {scalarData = scalarData}
        finiteMode oneLoop remainder rich running)
    depth →
  Bishop._≃_
    (Core.physicalTotalIncrement
      (EvaluatorBridge.asP3GSetoidPhysicalGeometry evaluator)
      (suc depth))
    (UV.embed
      (Plaquette.plaquetteCoefficientProjector
        (Plaquette.effectiveAction selectedAction depth)))
positiveEdgeP3GIsSelectedAction actionWeld evaluator depth =
  BishopP.≃-trans
    (Core.positiveEdgeTotalIncrementSameSource
      (EvaluatorBridge.asP3GSetoidPhysicalGeometry evaluator) depth)
    (Core.equalityAsBishopSetoid
      (cong UV.embed
        (Action.sourceBetaIsSelectedActionCoefficient actionWeld depth)))
