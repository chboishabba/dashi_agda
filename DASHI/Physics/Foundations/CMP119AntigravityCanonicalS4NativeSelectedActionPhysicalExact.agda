{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4NativeSelectedActionPhysicalExact where

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ)
import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4NativeSetoidSourceExact as NativeS4
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SetoidPhysicalPackageExact as S4
import DASHI.Physics.Foundations.CMP119AntigravityP3GNativeSetoidLiteralEvaluatorExact as Native
import DASHI.Physics.Foundations.CMP119AntigravityP3GNativeSetoidSelectedActionExact as Action
import DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalSignedQuarticReceiptExact as Signed
import DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalReceiptMajorantExact as Majorant
import DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidPhysicalCoreExact as Core
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteMode
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

------------------------------------------------------------------------
-- Preferred source packet for S4:
--   one literal evaluator -> one CMP109 beta -> one P3G setoid state
--   selected action termwise source -> SAME P3G positive-edge coefficient
--   rich receipts + signed quartic -> explicit two-sided Bishop majorant
--   Row-A cap -> SAME history threshold
--
-- This type has NO dependency on the legacy P3 running-coupling record.
-- The termwise/source evaluator and physical certificates remain genuine,
-- separately visible obligations. Do not infer their concrete inhabitants
-- merely from the constructors below.
------------------------------------------------------------------------

record CanonicalS4NativeSelectedActionSource
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
    source :
      NativeS4.CanonicalS4NativeSetoidSource
        {trajectory = trajectory} {split = split}
        {Mode = Mode} {Atom = Atom}
        {expressions = expressions} {ward = ward} {scalarData = scalarData}
        inputs rowA smallFieldCap largeFieldCap covarianceCap
        finiteMode oneLoop remainder rich

    selectedAction :
      Plaquette.ExactOneStepEffectiveActionData Nat

    selectedTerms :
      Action.SelectedActionOnNativeEvaluator
        (NativeS4.literalEvaluator source) selectedAction

    signedQuartic :
      Signed.PhysicalSignedQuarticSource
        (Native.asPhysicalGeometry (NativeS4.literalEvaluator source))

open CanonicalS4NativeSelectedActionSource public

asNativePhysicalS4 :
  ∀ {trajectory split Mode Atom expressions ward scalarData
       inputs rowA smallFieldCap largeFieldCap covarianceCap
       finiteMode oneLoop remainder rich}
    (packet : CanonicalS4NativeSelectedActionSource
      {trajectory = trajectory} {split = split}
      {Mode = Mode} {Atom = Atom}
      {expressions = expressions} {ward = ward} {scalarData = scalarData}
      inputs rowA smallFieldCap largeFieldCap covarianceCap
      finiteMode oneLoop remainder rich) →
  S4.CanonicalS4SetoidPhysicalPackage
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap
asNativePhysicalS4 packet =
  NativeS4.asPhysicalS4 (source packet)

physicalRemainderBoundFromSameSource :
  ∀ {trajectory split Mode Atom expressions ward scalarData
       inputs rowA smallFieldCap largeFieldCap covarianceCap
       finiteMode oneLoop remainder rich}
    (packet : CanonicalS4NativeSelectedActionSource
      {trajectory = trajectory} {split = split}
      {Mode = Mode} {Atom = Atom}
      {expressions = expressions} {ward = ward} {scalarData = scalarData}
      inputs rowA smallFieldCap largeFieldCap covarianceCap
      finiteMode oneLoop remainder rich) →
  S4.CanonicalS4SetoidControlledRemainder
    (asNativePhysicalS4 packet)
    (Majorant.physicalReceiptMajorant (signedQuartic packet))
physicalRemainderBoundFromSameSource packet =
  S4.controlledRemainderFromPhysicalReceipts
    (asNativePhysicalS4 packet)
    (signedQuartic packet)

p3GPositiveEdgeIsSameSelectedAction :
  ∀ {trajectory split Mode Atom expressions ward scalarData
       inputs rowA smallFieldCap largeFieldCap covarianceCap
       finiteMode oneLoop remainder rich}
    (packet : CanonicalS4NativeSelectedActionSource
      {trajectory = trajectory} {split = split}
      {Mode = Mode} {Atom = Atom}
      {expressions = expressions} {ward = ward} {scalarData = scalarData}
      inputs rowA smallFieldCap largeFieldCap covarianceCap
      finiteMode oneLoop remainder rich)
    k →
  Bishop._≃_
    (Core.physicalTotalIncrement
      (Native.asPhysicalGeometry
        (NativeS4.literalEvaluator (source packet))) (suc k))
    (UV.embed
      (Plaquette.plaquetteCoefficientProjector
        (Plaquette.effectiveAction (selectedAction packet) k)))
p3GPositiveEdgeIsSameSelectedAction packet =
  Action.p3GIncrementIsSelectedNonlinearAction (selectedTerms packet)
