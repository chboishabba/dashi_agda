{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3GNativeSetoidSelectedActionExact where

open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (cong)
import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityP3GNativeSetoidLiteralEvaluatorExact as Native
import DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidPhysicalCoreExact as Core
import DASHI.Physics.Foundations.CMP119AntigravitySelectedActionFiniteModePhysicalWeldExact as Weld
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteMode
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

------------------------------------------------------------------------
-- One truly native setoid source determines the SAME finite-mode plaquette
-- witness used by the action and P3G geometry. No second beta split field.
-- No CanonicalBishopSU2RunningInputs, no legacy P3 intensional recurrence.
------------------------------------------------------------------------

record SelectedActionOnNativeEvaluator
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom expressions ward scalarData : Set}
    {finiteMode : FiniteMode.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {oneLoop : Plaquette.OneLoopVacuumPolarizationData Nat}
    {remainder : Plaquette.PlaquetteRemainderData Nat}
    {rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ}
    (native : Native.NativeSetoidLiteralEvaluatorSource
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {expressions = expressions} {ward = ward} {scalarData = scalarData}
      finiteMode oneLoop remainder rich)
    (selectedAction : Plaquette.ExactOneStepEffectiveActionData Nat) : Set₁ where
  field
    background : ∀ k →
      Plaquette.backgroundSubstitutionPlaquetteCoefficient selectedAction k
      ≡ Plaquette.backgroundRemainder remainder k
    haar : ∀ k →
      Plaquette.haarJacobianPlaquetteCoefficient selectedAction k
      ≡ Plaquette.jacobianRemainder remainder k
    determinant : ∀ k →
      Plaquette.fluctuationDeterminantPlaquetteCoefficient selectedAction k
      ≡ Plaquette.determinantRemainder remainder k
    connected : ∀ k →
      Plaquette.connectedCumulantPlaquetteCoefficient selectedAction k
      ≡ Plaquette.vacuumPolarizationPlaquetteCoefficient oneLoop k
        + Plaquette.bchRemainder remainder k
    localization : ∀ k →
      Plaquette.localizationRemainderPlaquetteCoefficient selectedAction k
      ≡ Plaquette.localizationRemainder remainder k

open SelectedActionOnNativeEvaluator public

asFiniteModeActionWeld :
  ∀ {trajectory Mode Atom expressions ward scalarData
       finiteMode oneLoop remainder rich selectedAction native} →
  SelectedActionOnNativeEvaluator
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {expressions = expressions} {ward = ward} {scalarData = scalarData}
    {finiteMode = finiteMode} {oneLoop = oneLoop}
    {remainder = remainder} {rich = rich}
    native selectedAction →
  Weld.SelectedActionFiniteModePlaquetteIdentification
    finiteMode oneLoop remainder selectedAction
asFiniteModeActionWeld {native = native} same = record
  { Weld.SelectedActionFiniteModePlaquetteIdentification.finiteModePlaquette =
      Native.finiteModePlaquette native
  ; Weld.SelectedActionFiniteModePlaquetteIdentification.background =
      background same
  ; Weld.SelectedActionFiniteModePlaquetteIdentification.haar =
      haar same
  ; Weld.SelectedActionFiniteModePlaquetteIdentification.determinant =
      determinant same
  ; Weld.SelectedActionFiniteModePlaquetteIdentification.connected =
      connected same
  ; Weld.SelectedActionFiniteModePlaquetteIdentification.localization =
      localization same
  }

p3GIncrementIsSelectedNonlinearAction :
  ∀ {trajectory Mode Atom expressions ward scalarData
       finiteMode oneLoop remainder rich selectedAction native}
    (same : SelectedActionOnNativeEvaluator
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {expressions = expressions} {ward = ward} {scalarData = scalarData}
      {finiteMode = finiteMode} {oneLoop = oneLoop}
      {remainder = remainder} {rich = rich}
      native selectedAction)
    k →
  Bishop._≃_
    (Core.physicalTotalIncrement (Native.asPhysicalGeometry native) (suc k))
    (UV.embed
      (Plaquette.plaquetteCoefficientProjector
        (Plaquette.effectiveAction selectedAction k)))
p3GIncrementIsSelectedNonlinearAction {native = native} same k =
  BishopP.≃-trans
    (Core.positiveEdgeTotalIncrementSameSource
      (Native.asPhysicalGeometry native) k)
    (Core.equalityAsBishopSetoid
      (cong UV.embed
        (Weld.sourceBetaIsSelectedActionCoefficient
          (asFiniteModeActionWeld same) k)))
