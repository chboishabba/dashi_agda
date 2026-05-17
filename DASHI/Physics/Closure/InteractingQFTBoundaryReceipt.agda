module DASHI.Physics.Closure.InteractingQFTBoundaryReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.KleinGordonAQFTReceipt as KG

------------------------------------------------------------------------
-- Interacting-QFT boundary receipt.
--
-- This records the boundary after the free-field AQFT witness: the
-- Haag-Kastler/Klein-Gordon receipt gives a free-field point surface, while
-- interacting Standard Model / QCD-level QFT still requires renormalisation,
-- representation choices, empirical couplings, and additional constructive
-- existence witnesses.

data InteractingQFTPromotionAuthorityToken : Set where

data InteractingQFTFirstOpenObligation : Set where
  missingConstructiveInteractingNet :
    InteractingQFTFirstOpenObligation

  missingRenormalisationAdapter :
    InteractingQFTFirstOpenObligation

  missingEmpiricalCouplingCalibration :
    InteractingQFTFirstOpenObligation

record InteractingQFTBoundaryReceipt : Setω where
  field
    freeFieldWitness :
      KG.KleinGordonAQFTReceipt

    freeQFTHandledBy :
      String

    freeQFTHandledBy-v :
      freeQFTHandledBy ≡
        "AQFTNetReceipt-plus-KleinGordonAQFTReceipt"

    interactingQFTHandled :
      Bool

    interactingQFTHandled-v :
      interactingQFTHandled ≡ false

    renormalisationStatus :
      String

    renormalisationStatus-v :
      renormalisationStatus ≡
        "perturbative-renormalisation-is-coupling-calibration-adapter-not-structural-closure"

    couplingConstants :
      String

    couplingConstants-v :
      couplingConstants ≡
        "alpha-alphas-GF-GN-and-SM-couplings-are-empirical-adapters"

    firstOpenObligation :
      InteractingQFTFirstOpenObligation

    firstOpenObligation-v :
      firstOpenObligation ≡ missingConstructiveInteractingNet

    boundaryIsResult :
      Bool

    boundaryIsResult-v :
      boundaryIsResult ≡ true

    noSMQFTPromotionFromThisBoundary :
      Bool

    noSMQFTPromotionFromThisBoundary-v :
      noSMQFTPromotionFromThisBoundary ≡ true

    noGRQFTPromotionFromThisBoundary :
      Bool

    noGRQFTPromotionFromThisBoundary-v :
      noGRQFTPromotionFromThisBoundary ≡ true

    noPromotionWithoutAuthority :
      InteractingQFTPromotionAuthorityToken → ⊥

    boundaryGovernance :
      List String

open InteractingQFTBoundaryReceipt public

canonicalInteractingQFTBoundaryReceipt :
  InteractingQFTBoundaryReceipt
canonicalInteractingQFTBoundaryReceipt =
  record
    { freeFieldWitness =
        KG.canonicalKleinGordonAQFTReceipt
    ; freeQFTHandledBy =
        "AQFTNetReceipt-plus-KleinGordonAQFTReceipt"
    ; freeQFTHandledBy-v =
        refl
    ; interactingQFTHandled =
        false
    ; interactingQFTHandled-v =
        refl
    ; renormalisationStatus =
        "perturbative-renormalisation-is-coupling-calibration-adapter-not-structural-closure"
    ; renormalisationStatus-v =
        refl
    ; couplingConstants =
        "alpha-alphas-GF-GN-and-SM-couplings-are-empirical-adapters"
    ; couplingConstants-v =
        refl
    ; firstOpenObligation =
        missingConstructiveInteractingNet
    ; firstOpenObligation-v =
        refl
    ; boundaryIsResult =
        true
    ; boundaryIsResult-v =
        refl
    ; noSMQFTPromotionFromThisBoundary =
        true
    ; noSMQFTPromotionFromThisBoundary-v =
        refl
    ; noGRQFTPromotionFromThisBoundary =
        true
    ; noGRQFTPromotionFromThisBoundary-v =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundaryGovernance =
        "Free-field AQFT has a Klein-Gordon stack witness surface"
        ∷ "Interacting QFT remains blocked on constructive interacting local algebra nets"
        ∷ "Renormalisation is staged as an adapter/calibration procedure, not a structural derivation"
        ∷ "SM/QCD coupling constants remain empirical calibration adapters"
        ∷ "This boundary is a result: it names the first open QFT obligation without promoting it"
        ∷ []
    }

interactingQFTFirstOpenIsConstructiveNet :
  InteractingQFTBoundaryReceipt.firstOpenObligation
    canonicalInteractingQFTBoundaryReceipt
  ≡
  missingConstructiveInteractingNet
interactingQFTFirstOpenIsConstructiveNet =
  refl
