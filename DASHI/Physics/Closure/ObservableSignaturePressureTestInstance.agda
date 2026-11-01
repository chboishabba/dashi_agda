module DASHI.Physics.Closure.ObservableSignaturePressureTestInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
import DASHI.Physics.Closure.AlternativeCarrierSignatureStress as ACSS
import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
import DASHI.Physics.Closure.ObservableSignaturePressureTest as OSPT
import DASHI.Physics.Closure.ObservableTransportGaugeEntry as OTGE

------------------------------------------------------------------------
-- Canonical inhabited pressure-test path.
--
-- This file promotes exactly one canonical point through the observable gate
-- and the signature gate.  It does not recover gauge/matter and does not make
-- a Standard Model claim.

data CanonicalShiftState : Set where
  canonicalShift : CanonicalShiftState

canonicalObservableCarriers : OTGE.ObservableTransportCarriers
canonicalObservableCarriers = record
  { ObservableCarrier = CanonicalShiftState
  ; PhysicsCarrier = CanonicalShiftState
  }

canonicalObservableContract :
  OTGE.ObservableTransportContract canonicalObservableCarriers
canonicalObservableContract = record
  { transport = λ x → x
  ; observableProjection = λ x → x
  ; admissible = λ _ → ⊤
  ; transportStable = λ _ _ → ⊤
  ; projectionCoherent = λ _ _ → ⊤
  }

canonicalObservableGate :
  OTGE.ObservableTransportGaugeEntry canonicalObservableContract
canonicalObservableGate = record
  { gaugeEntryBoundary = λ _ → ⊤
  ; status = λ _ → OTGE.forced
  ; admissibilityWitness = λ _ _ → tt
  ; stabilityWitness = λ _ _ → tt
  ; coherenceWitness = λ _ _ → tt
  }

canonicalSignatureCarrier : ACSS.AlternativeCarrier
canonicalSignatureCarrier = record
  { Carrier = CanonicalShiftState
  ; QuadraticCarrier = ⊤
  }

canonicalSignatureBridge :
  CQSB.ContractionQuadraticToSignatureBridgeTheorem
canonicalSignatureBridge =
  CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem

canonicalSignatureContract :
  ACSS.CarrierSignatureStressContract canonicalSignatureCarrier
canonicalSignatureContract = record
  { toQuadratic = λ _ → tt
  ; signatureOf = λ _ →
      CQSB.ContractionQuadraticToSignatureBridgeTheorem.signature31Value
        canonicalSignatureBridge
  ; carrierInvariant = λ _ → ⊤
  ; transportCompatible = λ _ _ → ⊤
  ; signatureCompatible = λ _ _ → ⊤
  ; obstruction = λ _ → ⊤
  }

canonicalSignatureStress :
  ACSS.AlternativeCarrierSignatureStress canonicalSignatureContract
canonicalSignatureStress = record
  { status = λ _ → ACSS.forced
  ; stressReason = λ _ → ⊤
  ; forced31 = λ _ _ →
      CQSB.ContractionQuadraticToSignatureBridgeTheorem.signatureForced31
        canonicalSignatureBridge
  ; conditionalInvariant = λ _ _ → tt
  ; conditionalTransport = λ _ _ → tt
  ; conditionalSignature = λ _ _ → tt
  ; failedObstruction = λ _ _ → tt
  }

canonicalObservableSignaturePressureTest :
  OSPT.ObservableSignaturePressureTest
    canonicalObservableContract
    canonicalSignatureContract
canonicalObservableSignaturePressureTest = record
  { observableGate = canonicalObservableGate
  ; signatureStress = canonicalSignatureStress
  ; alignState = λ x → x
  ; pressureStatus = λ _ → OSPT.promotionReady
  ; readyWhenForced = λ _ _ _ → refl
  ; conditionalBoundary = λ _ _ → ⊤
  ; blockedBoundary = λ _ _ → ⊤
  ; heldBoundary = λ _ _ → ⊤
  ; noGaugeMatterRecoveryClaim = tt
  }

observableForced :
  OTGE.status canonicalObservableGate canonicalShift ≡ OTGE.forced
observableForced = refl

signatureForced :
  ACSS.status canonicalSignatureStress canonicalShift ≡ ACSS.forced
signatureForced = refl

canonicalPromotionReady :
  OSPT.pressureStatus
    canonicalObservableSignaturePressureTest
    canonicalShift
  ≡
  OSPT.promotionReady
canonicalPromotionReady = refl

canonicalPromotionReadyPoint :
  OSPT.PromotionReadyPressurePoint
    canonicalObservableSignaturePressureTest
    canonicalShift
canonicalPromotionReadyPoint =
  OSPT.promotionReadyPressurePoint
    canonicalObservableSignaturePressureTest
    canonicalShift
    observableForced
    signatureForced

canonicalForcedSignaturePoint :
  ACSS.CanonicalForcedSignaturePoint CanonicalShiftState
canonicalForcedSignaturePoint =
  ACSS.canonicalForcedSignaturePoint canonicalShift canonicalSignatureBridge
