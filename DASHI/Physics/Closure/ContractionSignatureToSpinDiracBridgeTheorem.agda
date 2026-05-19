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
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.QuadraticPolarization as QP

record ContractionSignatureToSpinDiracBridgeTheoremFromMinimal
  (C : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  field
    contractionSignatureBridge : CQSB.ContractionQuadraticToSignatureBridgeTheorem
    spinLocalLorentzBridge :
      SLLB.SpinLocalLorentzBridge C
    canonicalSpinDiracConsumer :
      CSDC.SpinDiracConsumerFromMinimal C
    spinDiracFromBridgeRoute :
      CSDC.SpinDiracConsumerFromMinimal C
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

contractionSignatureToSpinDiracBridgeFromMinimal :
  (C : MCPC.MinimalCrediblePhysicsClosure) →
  ContractionSignatureToSpinDiracBridgeTheoremFromMinimal C
contractionSignatureToSpinDiracBridgeFromMinimal C =
  let
    bridge = CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
    local = SLLB.spinLocalLorentzBridgeFromMinimal C
  in
  record
    { contractionSignatureBridge = bridge
    ; spinLocalLorentzBridge = local
    ; canonicalSpinDiracConsumer =
        CSDC.spinDiracConsumerFromMinimal C
    ; spinDiracFromBridgeRoute =
        SLLB.SpinLocalLorentzBridge.consumer local
    ; signatureForced31 =
        CQSB.ContractionQuadraticToSignatureBridgeTheorem.signatureForced31 bridge
    ; normalizedQuadratic =
        CQSB.ContractionQuadraticToSignatureBridgeTheorem.normalizedQuadratic bridge
    }

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
  let derived =
        contractionSignatureToSpinDiracBridgeFromMinimal
          MCCSI.minimumCredibleClosureShift
  in
  record
    { contractionSignatureBridge =
        ContractionSignatureToSpinDiracBridgeTheoremFromMinimal.contractionSignatureBridge
          derived
    ; spinLocalLorentzBridge =
        ContractionSignatureToSpinDiracBridgeTheoremFromMinimal.spinLocalLorentzBridge
          derived
    ; canonicalSpinDiracConsumer =
        ContractionSignatureToSpinDiracBridgeTheoremFromMinimal.canonicalSpinDiracConsumer
          derived
    ; spinDiracFromBridgeRoute =
        ContractionSignatureToSpinDiracBridgeTheoremFromMinimal.spinDiracFromBridgeRoute
          derived
    ; signatureForced31 =
        ContractionSignatureToSpinDiracBridgeTheoremFromMinimal.signatureForced31
          derived
    ; normalizedQuadratic =
        ContractionSignatureToSpinDiracBridgeTheoremFromMinimal.normalizedQuadratic
          derived
    }

spinDiracBridgeBoundary :
  (bridge : ContractionSignatureToSpinDiracBridgeTheorem) →
  CFQS.SignatureCliffordGaugeBoundary
    (CQSB.ContractionQuadraticToSignatureBridgeTheorem.strengthenedContraction
      (ContractionSignatureToSpinDiracBridgeTheorem.contractionSignatureBridge bridge))
spinDiracBridgeBoundary bridge =
  CQSB.signatureBridgeBoundary
    (ContractionSignatureToSpinDiracBridgeTheorem.contractionSignatureBridge bridge)
