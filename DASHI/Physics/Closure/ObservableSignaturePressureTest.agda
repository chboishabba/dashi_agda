module DASHI.Physics.Closure.ObservableSignaturePressureTest where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Physics.Closure.ObservableTransportGaugeEntry as OTGE
import DASHI.Physics.Closure.AlternativeCarrierSignatureStress as ACSS

------------------------------------------------------------------------
-- Combined pressure-test surface.
--
-- This module connects the two current physics pressure-test lanes:
--
--   1. observable transport as a gauge-entry gate
--   2. signature forcing under carrier variation
--
-- It deliberately stops before gauge/matter recovery.  A result can be ready
-- for the next promotion gate only when both local lanes are forced.

data PhysicsPressureStatus : Set where
  promotionReady : PhysicsPressureStatus
  conditionallyReady : PhysicsPressureStatus
  blocked : PhysicsPressureStatus
  held : PhysicsPressureStatus

record ObservableSignaturePressureTest
  {ℓO ℓP ℓA ℓS ℓC ℓB ℓQ ℓI ℓT ℓSG ℓOB ℓR : Level}
  {obsCarriers : OTGE.ObservableTransportCarriers {ℓO} {ℓP}}
  {sigCarrier : ACSS.AlternativeCarrier {ℓP} {ℓQ}}
  (obsContract :
    OTGE.ObservableTransportContract {ℓO} {ℓP} {ℓA} {ℓS} {ℓC}
      obsCarriers)
  (sigContract :
    ACSS.CarrierSignatureStressContract
      {ℓP} {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB}
      sigCarrier)
    : Set
        (lsuc
          (ℓO ⊔ ℓP ⊔ ℓA ⊔ ℓS ⊔ ℓC ⊔ ℓB ⊔
           ℓQ ⊔ ℓI ⊔ ℓT ⊔ ℓSG ⊔ ℓOB ⊔ ℓR)) where
  field
    observableGate :
      OTGE.ObservableTransportGaugeEntry
        {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} {ℓB}
        obsContract

    signatureStress :
      ACSS.AlternativeCarrierSignatureStress
        {ℓP} {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB} {ℓR}
        sigContract

    alignState :
      OTGE.PhysicsCarrier obsCarriers →
      ACSS.Carrier sigCarrier

    pressureStatus :
      OTGE.PhysicsCarrier obsCarriers →
      PhysicsPressureStatus

    readyWhenForced :
      (p : OTGE.PhysicsCarrier obsCarriers) →
      OTGE.status observableGate p ≡ OTGE.forced →
      ACSS.status signatureStress (alignState p) ≡ ACSS.forced →
      pressureStatus p ≡ promotionReady

    conditionalBoundary :
      (p : OTGE.PhysicsCarrier obsCarriers) →
      pressureStatus p ≡ conditionallyReady →
      Set

    blockedBoundary :
      (p : OTGE.PhysicsCarrier obsCarriers) →
      pressureStatus p ≡ blocked →
      Set

    heldBoundary :
      (p : OTGE.PhysicsCarrier obsCarriers) →
      pressureStatus p ≡ held →
      Set

    noGaugeMatterRecoveryClaim :
      ⊤

open ObservableSignaturePressureTest public

record PromotionReadyPressurePoint
  {ℓO ℓP ℓA ℓS ℓC ℓB ℓQ ℓI ℓT ℓSG ℓOB ℓR : Level}
  {obsCarriers : OTGE.ObservableTransportCarriers {ℓO} {ℓP}}
  {sigCarrier : ACSS.AlternativeCarrier {ℓP} {ℓQ}}
  {obsContract :
    OTGE.ObservableTransportContract {ℓO} {ℓP} {ℓA} {ℓS} {ℓC}
      obsCarriers}
  {sigContract :
    ACSS.CarrierSignatureStressContract
      {ℓP} {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB}
      sigCarrier}
  (test :
    ObservableSignaturePressureTest
      {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} {ℓB}
      {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB} {ℓR}
      obsContract sigContract)
  (p : OTGE.PhysicsCarrier obsCarriers)
    : Set (ℓA ⊔ ℓS ⊔ ℓC) where
  field
    observableForced :
      OTGE.status (observableGate test) p ≡ OTGE.forced

    signatureForced :
      ACSS.status (signatureStress test) (alignState test p)
      ≡
      ACSS.forced

    pressureReady :
      pressureStatus test p ≡ promotionReady

    forcedEntry :
      OTGE.ForcedGaugeEntry (observableGate test) p

open PromotionReadyPressurePoint public

promotionReadyPressurePoint :
  {ℓO ℓP ℓA ℓS ℓC ℓB ℓQ ℓI ℓT ℓSG ℓOB ℓR : Level}
  {obsCarriers : OTGE.ObservableTransportCarriers {ℓO} {ℓP}}
  {sigCarrier : ACSS.AlternativeCarrier {ℓP} {ℓQ}}
  {obsContract :
    OTGE.ObservableTransportContract {ℓO} {ℓP} {ℓA} {ℓS} {ℓC}
      obsCarriers}
  {sigContract :
    ACSS.CarrierSignatureStressContract
      {ℓP} {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB}
      sigCarrier}
  (test :
    ObservableSignaturePressureTest
      {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} {ℓB}
      {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB} {ℓR}
      obsContract sigContract) →
  (p : OTGE.PhysicsCarrier obsCarriers) →
  OTGE.status (observableGate test) p ≡ OTGE.forced →
  ACSS.status (signatureStress test) (alignState test p) ≡ ACSS.forced →
  PromotionReadyPressurePoint test p
promotionReadyPressurePoint test p obsForced sigForced =
  record
    { observableForced = obsForced
    ; signatureForced = sigForced
    ; pressureReady = readyWhenForced test p obsForced sigForced
    ; forcedEntry =
        OTGE.forcedEntryFromGate
          (observableGate test)
          p
          obsForced
    }

heldPressureTestNoRecoveryClaim :
  {ℓO ℓP ℓA ℓS ℓC ℓB ℓQ ℓI ℓT ℓSG ℓOB ℓR : Level}
  {obsCarriers : OTGE.ObservableTransportCarriers {ℓO} {ℓP}}
  {sigCarrier : ACSS.AlternativeCarrier {ℓP} {ℓQ}}
  {obsContract :
    OTGE.ObservableTransportContract {ℓO} {ℓP} {ℓA} {ℓS} {ℓC}
      obsCarriers}
  {sigContract :
    ACSS.CarrierSignatureStressContract
      {ℓP} {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB}
      sigCarrier}
  (test :
    ObservableSignaturePressureTest
      {ℓO} {ℓP} {ℓA} {ℓS} {ℓC} {ℓB}
      {ℓQ} {ℓI} {ℓT} {ℓSG} {ℓOB} {ℓR}
      obsContract sigContract) →
  noGaugeMatterRecoveryClaim test ≡ tt
heldPressureTestNoRecoveryClaim test = refl
