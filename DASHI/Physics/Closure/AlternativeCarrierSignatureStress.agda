module DASHI.Physics.Closure.AlternativeCarrierSignatureStress where

open import Agda.Primitive using (Level; Setω; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
import DASHI.Physics.Closure.DeltaToQuadraticBridgeTheorem as DQ

------------------------------------------------------------------------
-- Alternative-carrier signature stress classification.
--
-- This module does not claim that every carrier forces sig31.  It records
-- exactly which carrier-local witnesses are needed before a carrier variation
-- can be promoted from conditional/held/failed into the canonical forced path.

data SignatureStressStatus : Set where
  forced : SignatureStressStatus
  conditional : SignatureStressStatus
  failed : SignatureStressStatus
  held : SignatureStressStatus

record AlternativeCarrier
  {ℓC ℓQ : Level} : Set (lsuc (ℓC ⊔ ℓQ)) where
  field
    Carrier : Set ℓC
    QuadraticCarrier : Set ℓQ

open AlternativeCarrier public

record CarrierSignatureStressContract
  {ℓC ℓQ ℓI ℓT ℓS ℓO : Level}
  (carrier : AlternativeCarrier {ℓC} {ℓQ})
    : Set (lsuc (ℓC ⊔ ℓQ ⊔ ℓI ⊔ ℓT ⊔ ℓS ⊔ ℓO)) where
  field
    toQuadratic :
      Carrier carrier →
      QuadraticCarrier carrier

    signatureOf :
      Carrier carrier →
      CTI.Signature

    carrierInvariant :
      Carrier carrier →
      Set ℓI

    transportCompatible :
      (x : Carrier carrier) →
      carrierInvariant x →
      Set ℓT

    signatureCompatible :
      (x : Carrier carrier) →
      carrierInvariant x →
      Set ℓS

    obstruction :
      Carrier carrier →
      Set ℓO

open CarrierSignatureStressContract public

record AlternativeCarrierSignatureStress
  {ℓC ℓQ ℓI ℓT ℓS ℓO ℓR : Level}
  {carrier : AlternativeCarrier {ℓC} {ℓQ}}
  (contract :
    CarrierSignatureStressContract
      {ℓC} {ℓQ} {ℓI} {ℓT} {ℓS} {ℓO}
      carrier)
    : Set (lsuc (ℓC ⊔ ℓQ ⊔ ℓI ⊔ ℓT ⊔ ℓS ⊔ ℓO ⊔ ℓR)) where
  field
    status :
      Carrier carrier →
      SignatureStressStatus

    stressReason :
      Carrier carrier →
      Set ℓR

    forced31 :
      (x : Carrier carrier) →
      status x ≡ forced →
      signatureOf contract x ≡ CTI.sig31

    conditionalInvariant :
      (x : Carrier carrier) →
      status x ≡ conditional →
      carrierInvariant contract x

    conditionalTransport :
      (x : Carrier carrier) →
      (s : status x ≡ conditional) →
      transportCompatible contract x (conditionalInvariant x s)

    conditionalSignature :
      (x : Carrier carrier) →
      (s : status x ≡ conditional) →
      signatureCompatible contract x (conditionalInvariant x s)

    failedObstruction :
      (x : Carrier carrier) →
      status x ≡ failed →
      obstruction contract x

open AlternativeCarrierSignatureStress public

record SignatureStressReport
  {ℓC ℓQ ℓI ℓT ℓS ℓO ℓR : Level}
  {carrier : AlternativeCarrier {ℓC} {ℓQ}}
  {contract :
    CarrierSignatureStressContract
      {ℓC} {ℓQ} {ℓI} {ℓT} {ℓS} {ℓO}
      carrier}
  (stress :
    AlternativeCarrierSignatureStress
      {ℓC} {ℓQ} {ℓI} {ℓT} {ℓS} {ℓO} {ℓR}
      contract)
  (x : Carrier carrier)
    : Set (ℓR) where
  field
    classifiedAs :
      SignatureStressStatus

    classificationAgrees :
      status stress x ≡ classifiedAs

    reason :
      stressReason stress x

open SignatureStressReport public

classifySignatureStress :
  {ℓC ℓQ ℓI ℓT ℓS ℓO ℓR : Level}
  {carrier : AlternativeCarrier {ℓC} {ℓQ}}
  {contract :
    CarrierSignatureStressContract
      {ℓC} {ℓQ} {ℓI} {ℓT} {ℓS} {ℓO}
      carrier}
  (stress :
    AlternativeCarrierSignatureStress
      {ℓC} {ℓQ} {ℓI} {ℓT} {ℓS} {ℓO} {ℓR}
      contract) →
  (x : Carrier carrier) →
  stressReason stress x →
  SignatureStressReport stress x
classifySignatureStress stress x reason =
  record
    { classifiedAs = status stress x
    ; classificationAgrees = refl
    ; reason = reason
    }

------------------------------------------------------------------------
-- Canonical bridge lifts.
--
-- If an existing canonical bridge already supplies sig31, a carrier point can
-- be reported as forced only through that supplied bridge evidence.

record CanonicalForcedSignaturePoint {ℓC : Level} (Carrier : Set ℓC)
    : Setω where
  field
    point :
      Carrier

    bridge :
      CQSB.ContractionQuadraticToSignatureBridgeTheorem

    signatureValue :
      CTI.Signature

    signatureValueFromBridge :
      signatureValue
      ≡
      CQSB.ContractionQuadraticToSignatureBridgeTheorem.signature31Value bridge

    signatureForced31 :
      signatureValue ≡ CTI.sig31

open CanonicalForcedSignaturePoint public

canonicalForcedSignaturePoint :
  {ℓC : Level}
  {Carrier : Set ℓC} →
  Carrier →
  CQSB.ContractionQuadraticToSignatureBridgeTheorem →
  CanonicalForcedSignaturePoint Carrier
canonicalForcedSignaturePoint x bridge =
  record
    { point = x
    ; bridge = bridge
    ; signatureValue =
        CQSB.ContractionQuadraticToSignatureBridgeTheorem.signature31Value
          bridge
    ; signatureValueFromBridge = refl
    ; signatureForced31 =
        CQSB.ContractionQuadraticToSignatureBridgeTheorem.signatureForced31
          bridge
    }

deltaBridgeForcedSignaturePoint :
  {ℓC : Level}
  {Carrier : Set ℓC} →
  Carrier →
  DQ.DeltaToQuadraticBridgeTheorem →
  CanonicalForcedSignaturePoint Carrier
deltaBridgeForcedSignaturePoint x deltaBridge =
  canonicalForcedSignaturePoint
    x
    (DQ.DeltaToQuadraticBridgeTheorem.contractionQuadraticToSignatureBridge
      deltaBridge)

------------------------------------------------------------------------
-- Held surface for protected or deliberately deferred carriers.

record HeldCarrierSignatureStress {ℓC : Level} (Carrier : Set ℓC)
    : Set (lsuc ℓC) where
  field
    heldCarrier :
      Carrier

    heldReason :
      Set

    noSignatureClaim :
      ⊤

open HeldCarrierSignatureStress public

heldCarrierSignatureStress :
  {ℓC : Level}
  {Carrier : Set ℓC} →
  Carrier →
  Set →
  HeldCarrierSignatureStress Carrier
heldCarrierSignatureStress x reason =
  record
    { heldCarrier = x
    ; heldReason = reason
    ; noSignatureClaim = tt
    }
