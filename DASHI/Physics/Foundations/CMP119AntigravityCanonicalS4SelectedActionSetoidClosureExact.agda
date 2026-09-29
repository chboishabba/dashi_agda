{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SelectedActionSetoidClosureExact where

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ)
import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4FromLiteralEvaluatorSetoidExact as LiteralS4
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SetoidPhysicalPackageExact as S4
import DASHI.Physics.Foundations.CMP119AntigravityP3GFromLiteralEvaluatorFiniteModeExact as FromEvaluator
import DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidPhysicalCoreExact as Core
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalSignedQuarticReceiptExact as Signed
import DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalReceiptMajorantExact as Majorant
import DASHI.Physics.Foundations.CMP119AntigravityP3GSelectedActionFiniteModeEdgeExact as ActionEdge
import DASHI.Physics.Foundations.CMP119AntigravitySelectedActionFiniteModePhysicalWeldExact as Action
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteMode
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

------------------------------------------------------------------------
-- Single selected-source entrypoint: no duplicate P3, no independent beta/
-- action equality, and no post-hoc remainder estimates. All source-facing
-- physical obligations are visible and indexed by the SAME finite-mode packet.
------------------------------------------------------------------------

record CanonicalS4SelectedActionPhysicalSource
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
    literalSource :
      LiteralS4.CanonicalS4LiteralEvaluatorSource
        {trajectory = trajectory} {split = split}
        {Mode = Mode} {Atom = Atom}
        {expressions = expressions} {ward = ward} {scalarData = scalarData}
        inputs rowA smallFieldCap largeFieldCap covarianceCap
        finiteMode oneLoop remainder rich running

    selectedEffectiveAction :
      Plaquette.ExactOneStepEffectiveActionData Nat

    selectedTermwiseWeld :
      Action.SelectedActionFiniteModePlaquetteIdentification
        finiteMode oneLoop remainder selectedEffectiveAction

    signedQuarticSource :
      Signed.PhysicalSignedQuarticSource
        (FromEvaluator.asP3GSetoidPhysicalGeometry
          (LiteralS4.evaluatorSameObject literalSource))

open CanonicalS4SelectedActionPhysicalSource public

asCanonicalSetoidS4 :
  ∀ {trajectory split Mode Atom expressions ward scalarData
       inputs rowA smallFieldCap largeFieldCap covarianceCap
       finiteMode oneLoop remainder rich running}
    (source : CanonicalS4SelectedActionPhysicalSource
      {trajectory = trajectory} {split = split}
      {Mode = Mode} {Atom = Atom}
      {expressions = expressions} {ward = ward} {scalarData = scalarData}
      inputs rowA smallFieldCap largeFieldCap covarianceCap
      finiteMode oneLoop remainder rich running) →
  S4.CanonicalS4SetoidPhysicalPackage
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap
asCanonicalSetoidS4 source =
  LiteralS4.asCanonicalSetoidS4 (literalSource source)

controlledPhysicalRemainder :
  ∀ {trajectory split Mode Atom expressions ward scalarData
       inputs rowA smallFieldCap largeFieldCap covarianceCap
       finiteMode oneLoop remainder rich running}
    (source : CanonicalS4SelectedActionPhysicalSource
      {trajectory = trajectory} {split = split}
      {Mode = Mode} {Atom = Atom}
      {expressions = expressions} {ward = ward} {scalarData = scalarData}
      inputs rowA smallFieldCap largeFieldCap covarianceCap
      finiteMode oneLoop remainder rich running) →
  S4.CanonicalS4SetoidControlledRemainder
    (asCanonicalSetoidS4 source)
    (Majorant.physicalReceiptMajorant (signedQuarticSource source))
controlledPhysicalRemainder source =
  S4.controlledRemainderFromPhysicalReceipts
    (asCanonicalSetoidS4 source)
    (signedQuarticSource source)

selectedActionOwnsP3GEdge :
  ∀ {trajectory split Mode Atom expressions ward scalarData
       inputs rowA smallFieldCap largeFieldCap covarianceCap
       finiteMode oneLoop remainder rich running}
    (source : CanonicalS4SelectedActionPhysicalSource
      {trajectory = trajectory} {split = split}
      {Mode = Mode} {Atom = Atom}
      {expressions = expressions} {ward = ward} {scalarData = scalarData}
      inputs rowA smallFieldCap largeFieldCap covarianceCap
      finiteMode oneLoop remainder rich running)
    k →
  Bishop._≃_
    (Core.physicalTotalIncrement
      (FromEvaluator.asP3GSetoidPhysicalGeometry
        (LiteralS4.evaluatorSameObject (literalSource source)))
      (suc k))
    (UV.embed
      (Plaquette.plaquetteCoefficientProjector
        (Plaquette.effectiveAction (selectedEffectiveAction source) k)))
selectedActionOwnsP3GEdge source =
  ActionEdge.positiveEdgeP3GIsSelectedAction
    (selectedTermwiseWeld source)
    (LiteralS4.evaluatorSameObject (literalSource source))
