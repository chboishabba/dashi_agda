module DASHI.Physics.Closure.ContractionSignatureToSpinDiracBridgeTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.CanonicalSpinDiracConsumer as CSDC
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.SpinLocalLorentzBridgeTheorem as SLLB
open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.QuadraticPolarization as QP

record ContractionSignatureToSpinDiracBridgeTheorem : Setω where
  field
    contractionSignatureBridge : CQSB.ContractionQuadraticToSignatureBridgeTheorem
    spinLocalLorentzBridge :
      SLLB.SpinLocalLorentzBridge MCCSI.minimumCredibleClosureShift
    canonicalSpinDiracConsumer :
      CSDC.SpinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    spinDiracFromBridgeRoute :
      CSDC.SpinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    signatureForced31 :
      CQSB.ContractionQuadraticToSignatureBridgeTheorem.signature31Value
        contractionSignatureBridge
      ≡ CTI.sig31
    normalizedQuadratic :
      ∀ x →
        QF.QuadraticForm.Q
          (CFQS.ContractionForcesQuadraticStrong.derivedQuadratic
            (CQSB.ContractionQuadraticToSignatureBridgeTheorem.strengthenedContraction
              contractionSignatureBridge))
          x
        ≡ QP.Q̂core x

canonicalContractionSignatureToSpinDiracBridgeTheorem :
  ContractionSignatureToSpinDiracBridgeTheorem
canonicalContractionSignatureToSpinDiracBridgeTheorem =
  let
    bridge = CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
  in
  record
    { contractionSignatureBridge = bridge
    ; spinLocalLorentzBridge = SLLB.canonicalSpinLocalLorentzBridge
    ; canonicalSpinDiracConsumer =
        CSDC.spinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    ; spinDiracFromBridgeRoute =
        SLLB.SpinLocalLorentzBridge.consumer
          SLLB.canonicalSpinLocalLorentzBridge
    ; signatureForced31 =
        CQSB.ContractionQuadraticToSignatureBridgeTheorem.signatureForced31 bridge
    ; normalizedQuadratic =
        CQSB.ContractionQuadraticToSignatureBridgeTheorem.normalizedQuadratic bridge
    }
