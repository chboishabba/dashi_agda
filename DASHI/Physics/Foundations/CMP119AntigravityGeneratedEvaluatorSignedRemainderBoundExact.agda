{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityGeneratedEvaluatorSignedRemainderBoundExact where

------------------------------------------------------------------------
-- COMPLETE QUANTITATIVE RECEIPT COMPILER FROM ONE GENERATED SOURCE
--
-- The Bishop rich order is fixed definitionally. The regular partition
-- is the literal evaluator's generated four-orbit grid definitionally.
-- Thus neither a separate partition same-object law nor an order transport
-- law is assumed. The remaining physical data are the literal Gaussian
-- shell/epsilon match and the actual signed quartic certificate.
--
-- The output is an explicit |boxLower - C*g^4| + |boxUpper + C*g^4|
-- majorant of the SAME native P3G positive-edge remainder.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityGeneratedRichFromSelectedLiteralEvaluatorExact as Generated
import DASHI.Physics.Foundations.CMP119AntigravityGeneratedRichFiniteModeP3GExact as NativeFromGenerated
import DASHI.Physics.Foundations.CMP119AntigravityP3GNativeSetoidLiteralEvaluatorExact as Native
import DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalSignedQuarticReceiptExact as Signed
import DASHI.Physics.Foundations.CMP119AntigravityP3GPhysicalReceiptMajorantExact as Majorant
import DASHI.Physics.Foundations.CMP119AntigravityFiniteModePlaquetteBetaSameObjectExact as Same
import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidPhysicalCoreExact as Core
import DASHI.Physics.YangMills.BalabanYM4LiteralPlaquetteBetaEstimateExact as Literal
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as Finite
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette

module _
  {trajectory Mode Atom expressions ward scalarData}
  {finiteMode : Finite.FiniteModeBetaTrajectoryData trajectory Mode Atom}
  {oneLoop : Plaquette.OneLoopVacuumPolarizationData Nat}
  {remainder : Plaquette.PlaquetteRemainderData Nat}
  {evaluatorAt}
  {selected : Generated.SelectedEvaluatorGeneratedRichSource
    {expressions = expressions} {ward = ward} {scalarData = scalarData}
    evaluatorAt}
  (physical : NativeFromGenerated.GeneratedSelectedFiniteModePhysicalWeld
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {expressions = expressions} {ward = ward} {scalarData = scalarData}
    finiteMode oneLoop remainder {evaluatorAt = evaluatorAt} selected)
  where

  sourceWeld =
    Same.asCMP109LiteralPlaquetteCoefficientWeld
      (NativeFromGenerated.finiteModePlaquette physical)

  physicalGeometry =
    Native.asPhysicalGeometry
      (NativeFromGenerated.asNativeSelectedEvaluator physical)

  sourceSignedQuartic :
    (certificate : ∀ k →
      Literal.LiteralFiniteBetaCertificate
        (Constructor.asPhysicalRunningCouplingData sourceWeld) k) →
    Signed.PhysicalSignedQuarticSource physicalGeometry
  sourceSignedQuartic certificate = record
    { Signed.PhysicalSignedQuarticSource.richOrderSound =
        λ _ _ order → order
    ; Signed.PhysicalSignedQuarticSource.certificate = certificate
    }

  selectedPhysicalRemainderMajorant :
    (certificate : ∀ k →
      Literal.LiteralFiniteBetaCertificate
        (Constructor.asPhysicalRunningCouplingData sourceWeld) k) →
    Nat → Bishop.ℝ
  selectedPhysicalRemainderMajorant certificate =
    Majorant.physicalReceiptMajorant
      (sourceSignedQuartic certificate)

  selectedPhysicalRemainderControlled :
    (certificate : ∀ k →
      Literal.LiteralFiniteBetaCertificate
        (Constructor.asPhysicalRunningCouplingData sourceWeld) k) →
    Majorant.Running.PhysicalRemainderMajorant
      (Majorant.Running.fromPhysicalCore physicalGeometry)
      (selectedPhysicalRemainderMajorant certificate)
  selectedPhysicalRemainderControlled certificate =
    Majorant.asPhysicalRemainderMajorant
      (sourceSignedQuartic certificate)
