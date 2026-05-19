module DASHI.Physics.Closure.W4MatterStressEnergyInterfaceReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as W4External

------------------------------------------------------------------------
-- W4 matter/stress-energy interface receipt.
--
-- This is a pre-GR contract surface.  It records the minimum Candidate256
-- physical-calibration payload needed before W4 matter and stress-energy
-- can be named as typed consumers.  It does not construct matter, stress
-- energy, a discrete Einstein law, a GR law, a QFT law, or a GR/QFT
-- promotion.

record W4MatterStressEnergyPreflightSurface : Setω where
  field
    MatterField :
      Set

    T_mu_nu :
      MatterField →
      Set

    matterFieldFromW4 :
      W4External.Candidate256PhysicalCalibrationExternalReceipt →
      MatterField

    stressEnergyTensorFromW4 :
      (matter : MatterField) →
      T_mu_nu matter

    preflightBoundary :
      List String

record W4MatterStressEnergyPromotion : Setω where
  field
    candidate256PhysicalCalibrationReceipt :
      W4External.Candidate256PhysicalCalibrationExternalReceipt

    preflightSurface :
      W4MatterStressEnergyPreflightSurface

    matterField :
      W4MatterStressEnergyPreflightSurface.MatterField preflightSurface

    stressEnergyTensor :
      W4MatterStressEnergyPreflightSurface.T_mu_nu
        preflightSurface
        matterField

    promotionBoundary :
      List String

Candidate256PhysicalCalibrationExternalReceiptMissing : Setω
Candidate256PhysicalCalibrationExternalReceiptMissing =
  W4External.Candidate256PhysicalCalibrationExternalReceipt →
  ⊥

notCandidate256ToNoW4MatterStressEnergyPromotion :
  Candidate256PhysicalCalibrationExternalReceiptMissing →
  W4MatterStressEnergyPromotion →
  ⊥
notCandidate256ToNoW4MatterStressEnergyPromotion missingCandidate256 promotion =
  missingCandidate256
    (W4MatterStressEnergyPromotion.candidate256PhysicalCalibrationReceipt
      promotion)

candidate256MissingHere :
  Candidate256PhysicalCalibrationExternalReceiptMissing
candidate256MissingHere =
  W4External.candidate256PhysicalCalibrationExternalReceiptImpossibleHere

w4MatterStressEnergyPromotionImpossibleHere :
  W4MatterStressEnergyPromotion →
  ⊥
w4MatterStressEnergyPromotionImpossibleHere =
  notCandidate256ToNoW4MatterStressEnergyPromotion candidate256MissingHere

data W4StressEnergyMatterComponent : Set where
  energyDensityT00 :
    W4StressEnergyMatterComponent
  radialPressureT11 :
    W4StressEnergyMatterComponent
  tangentialPressureT22 :
    W4StressEnergyMatterComponent
  tangentialPressureT33 :
    W4StressEnergyMatterComponent
  offDiagonalConvention :
    W4StressEnergyMatterComponent

canonicalW4StressEnergyMatterComponents :
  List W4StressEnergyMatterComponent
canonicalW4StressEnergyMatterComponents =
  energyDensityT00
  ∷ radialPressureT11
  ∷ tangentialPressureT22
  ∷ tangentialPressureT33
  ∷ offDiagonalConvention
  ∷ []

data W4StressEnergyUnitAuthorityBlocker : Set where
  missingEnergyDensityUnits :
    W4StressEnergyUnitAuthorityBlocker
  missingPressureUnits :
    W4StressEnergyUnitAuthorityBlocker
  missingMassWindowBinding :
    W4StressEnergyUnitAuthorityBlocker
  missingAcceptanceDefinition :
    W4StressEnergyUnitAuthorityBlocker
  missingVolumeElementOrBinVolume :
    W4StressEnergyUnitAuthorityBlocker
  missingSourceUnitConvention :
    W4StressEnergyUnitAuthorityBlocker
  missingW4AuthorityBackedMatterNormalization :
    W4StressEnergyUnitAuthorityBlocker

canonicalW4StressEnergyUnitAuthorityBlockers :
  List W4StressEnergyUnitAuthorityBlocker
canonicalW4StressEnergyUnitAuthorityBlockers =
  missingEnergyDensityUnits
  ∷ missingPressureUnits
  ∷ missingMassWindowBinding
  ∷ missingAcceptanceDefinition
  ∷ missingVolumeElementOrBinVolume
  ∷ missingSourceUnitConvention
  ∷ missingW4AuthorityBackedMatterNormalization
  ∷ []

record W4StressEnergyMatterComponentRequest : Setω where
  field
    requestStatus :
      String

    targetTensorName :
      String

    targetMatterFieldName :
      String

    requestedComponents :
      List W4StressEnergyMatterComponent

    requestedComponentsAreCanonical :
      requestedComponents ≡ canonicalW4StressEnergyMatterComponents

    exactUnitAuthorityBlockers :
      List W4StressEnergyUnitAuthorityBlocker

    exactUnitAuthorityBlockersAreCanonical :
      exactUnitAuthorityBlockers ≡ canonicalW4StressEnergyUnitAuthorityBlockers

    energyDensityRequest :
      String

    pressureRequest :
      String

    massWindowRequest :
      String

    acceptanceRequest :
      String

    volumeRequest :
      String

    sourceUnitRequest :
      String

    diagonalEvidenceBoundary :
      List String

    authorityBoundary :
      List String

    promotesW4 :
      Bool

    promotesW4IsFalse :
      promotesW4 ≡ false

    constructsMatterField :
      Bool

    constructsMatterFieldIsFalse :
      constructsMatterField ≡ false

    constructsStressEnergyTensor :
      Bool

    constructsStressEnergyTensorIsFalse :
      constructsStressEnergyTensor ≡ false

    noPromotionWithoutCandidate256 :
      W4MatterStressEnergyPromotion →
      ⊥

    noW4PromotionWitness :
      ⊤

canonicalW4StressEnergyMatterComponentRequest :
  W4StressEnergyMatterComponentRequest
canonicalW4StressEnergyMatterComponentRequest =
  record
    { requestStatus =
        "blocked: exact T_matter component/unit authority missing"
    ; targetTensorName =
        "T_matter_mu_nu / T_mu_nu"
    ; targetMatterFieldName =
        "MatterField derived from accepted W4 calibration authority"
    ; requestedComponents =
        canonicalW4StressEnergyMatterComponents
    ; requestedComponentsAreCanonical =
        refl
    ; exactUnitAuthorityBlockers =
        canonicalW4StressEnergyUnitAuthorityBlockers
    ; exactUnitAuthorityBlockersAreCanonical =
        refl
    ; energyDensityRequest =
        "energyDensityT00 : accepted energy density rho in the same source units used by the W4 matter field"
    ; pressureRequest =
        "pressure components : accepted diagonal pressure convention for T11, T22, T33, plus off-diagonal zero/nonzero convention"
    ; massWindowRequest =
        "massWindow : accepted invariant-mass window binding the W4 Z/below-Z evidence to the matter source"
    ; acceptanceRequest =
        "acceptance : accepted detector/phase-space acceptance and lepton-channel combination convention"
    ; volumeRequest =
        "volume : accepted bin volume, luminosity-normalized volume element, or explicit statement that no volume conversion is used"
    ; sourceUnitRequest =
        "sourceUnits : accepted conversion tying cross-section/luminosity/bin evidence to stress-energy units"
    ; diagonalEvidenceBoundary =
        "Accepted diagonal/Z evidence is not by itself a stress-energy tensor"
        ∷ "The diagonal evidence must be converted into rho and pressure components through an authority-backed unit convention"
        ∷ "Mass window, acceptance, volume, and source units must be part of the same accepted request payload"
        ∷ []
    ; authorityBoundary =
        "No W4 matter field is defined from public-source evidence without Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "No T_matter component is promoted from diagonal/Z evidence without accepted source units"
        ∷ "No Einstein source term is promoted until the W4 matter/stress-energy interface receipt is inhabited"
        ∷ []
    ; promotesW4 =
        false
    ; promotesW4IsFalse =
        refl
    ; constructsMatterField =
        false
    ; constructsMatterFieldIsFalse =
        refl
    ; constructsStressEnergyTensor =
        false
    ; constructsStressEnergyTensorIsFalse =
        refl
    ; noPromotionWithoutCandidate256 =
        w4MatterStressEnergyPromotionImpossibleHere
    ; noW4PromotionWitness =
        tt
    }

record W4MatterStressEnergyInterfaceContractStatus : Setω where
  field
    requiredCalibrationReceiptName :
      String

    matterFieldFromW4TargetShape :
      String

    stressEnergyTensorFromW4TargetShape :
      String

    stressEnergyMatterComponentRequest :
      W4StressEnergyMatterComponentRequest

    orderedContractPath :
      List String

    missingGap :
      String

    governanceBoundary :
      List String

    noPromotionWithoutCandidate256 :
      W4MatterStressEnergyPromotion →
      ⊥

canonicalW4MatterStressEnergyInterfaceContractStatus :
  W4MatterStressEnergyInterfaceContractStatus
canonicalW4MatterStressEnergyInterfaceContractStatus =
  record
    { requiredCalibrationReceiptName =
        "DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation.Candidate256PhysicalCalibrationExternalReceipt"
    ; matterFieldFromW4TargetShape =
        "matterFieldFromW4 : Candidate256PhysicalCalibrationExternalReceipt -> MatterField"
    ; stressEnergyTensorFromW4TargetShape =
        "stressEnergyTensorFromW4 : MatterField -> T_mu_nu"
    ; stressEnergyMatterComponentRequest =
        canonicalW4StressEnergyMatterComponentRequest
    ; orderedContractPath =
        "Candidate256 calibration receipt"
        ∷ "MatterField"
        ∷ "energy density rho / T00 units"
        ∷ "pressure components / T11 T22 T33 units"
        ∷ "mass window, acceptance, volume, and source-unit convention"
        ∷ "T_mu_nu"
        ∷ "discrete Einstein law obligation"
        ∷ []
    ; missingGap =
        "Missing Candidate256 physical calibration receipt and exact T_matter unit/authority payload"
    ; governanceBoundary =
        "No W4 matter field can be consumed from Candidate256 without Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "No W4 stress-energy tensor can be promoted without a W4 matter field derived behind that receipt"
        ∷ "Accepted diagonal/Z evidence does not define energy density, pressure, mass-window binding, acceptance, volume, or source units by itself"
        ∷ "This module does not construct Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "This module does not construct W4MatterStressEnergyPromotion"
        ∷ "This module does not define grEquationLaw"
        ∷ "This module does not promote GR, QFT, GR/QFT, W4, or W5"
        ∷ []
    ; noPromotionWithoutCandidate256 =
        w4MatterStressEnergyPromotionImpossibleHere
    }
