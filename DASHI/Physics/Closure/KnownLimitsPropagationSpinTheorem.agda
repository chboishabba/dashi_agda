module DASHI.Physics.Closure.KnownLimitsPropagationSpinTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.Closure.CanonicalSpinDiracConsumer as CSDC
open import DASHI.Physics.Closure.ContractionSignatureToSpinDiracBridgeTheorem as CSSDB
open import DASHI.Physics.Closure.KnownLimitsEffectiveGeometryTheorem as KLET
open import DASHI.Physics.Closure.KnownLimitsLocalRecoveryTheorem as KLRT
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.Closure.SpinLocalLorentzBridgeTheorem as SLLB
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record KnownLimitsPropagationSpinTheorem : Setω where
  field
    contractionSignatureToSpinDiracBridge :
      CSSDB.ContractionSignatureToSpinDiracBridgeTheorem
    spinLocalLorentzBridge :
      SLLB.SpinLocalLorentzBridge MCCSI.minimumCredibleClosureShift
    localRecovery : KLRT.KnownLimitsLocalRecoveryTheorem
    effectiveGeometry : KLET.KnownLimitsEffectiveGeometryTheorem
    canonicalConsumer :
      CSDC.SpinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    propagationSeams : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    effectiveOrthogonality : ∀ {m : Nat} → OZ.OrthogonalityZLift {m}
    effectivePolarization :
      ∀ {m : Nat} →
      OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ

canonicalKnownLimitsPropagationSpinTheorem :
  KnownLimitsPropagationSpinTheorem
canonicalKnownLimitsPropagationSpinTheorem =
  record
    { contractionSignatureToSpinDiracBridge =
        CSSDB.canonicalContractionSignatureToSpinDiracBridgeTheorem
    ; spinLocalLorentzBridge = SLLB.canonicalSpinLocalLorentzBridge
    ; localRecovery = KLRT.canonicalKnownLimitsLocalRecoveryTheorem
    ; effectiveGeometry = KLET.canonicalKnownLimitsEffectiveGeometryTheorem
    ; canonicalConsumer =
        CSDC.spinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    ; propagationSeams =
        KLET.KnownLimitsEffectiveGeometryTheorem.propagationSeams
          KLET.canonicalKnownLimitsEffectiveGeometryTheorem
    ; effectiveOrthogonality =
        KLET.KnownLimitsEffectiveGeometryTheorem.effectiveOrthogonality
          KLET.canonicalKnownLimitsEffectiveGeometryTheorem
    ; effectivePolarization =
        KLET.KnownLimitsEffectiveGeometryTheorem.effectivePolarization
          KLET.canonicalKnownLimitsEffectiveGeometryTheorem
    }
