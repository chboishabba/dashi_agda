module DASHI.Physics.QFT.DHRSectorFunctoriality where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.DHRGaugeReceiptSurface as DHR
import DASHI.Physics.QFT.DHRThermodynamicLimit as DHRLimit

------------------------------------------------------------------------
-- DHR sector functoriality.
--
-- This is a typed interface package, not a new parallel reconstruction
-- formalism.  It exposes the existing DHR primitive surfaces in the shape
-- required by the next reusable theorem layer:
--   objects = localised transportable endomorphisms,
--   morphisms = intertwiners,
--   transport = inclusion-compatible localisation,
--   tensor = sector composition,
--   reconstruction = compatibility with the colimit boundary.

data DHRSectorFunctorialityStatus : Set where
  boundaryOnlyNoPromotion :
    DHRSectorFunctorialityStatus

data DHRSectorFunctorialityOpenObligation : Set where
  missingObjectFunctoriality :
    DHRSectorFunctorialityOpenObligation

  missingMorphismFunctoriality :
    DHRSectorFunctorialityOpenObligation

  missingTransportAlongInclusions :
    DHRSectorFunctorialityOpenObligation

  missingTensorProductLaw :
    DHRSectorFunctorialityOpenObligation

  missingReconstructionCompatibility :
    DHRSectorFunctorialityOpenObligation

  missingGate6Promotion :
    DHRSectorFunctorialityOpenObligation

canonicalDHRSectorFunctorialityOpenObligations :
  List DHRSectorFunctorialityOpenObligation
canonicalDHRSectorFunctorialityOpenObligations =
  missingObjectFunctoriality
  ∷ missingMorphismFunctoriality
  ∷ missingTransportAlongInclusions
  ∷ missingTensorProductLaw
  ∷ missingReconstructionCompatibility
  ∷ missingGate6Promotion
  ∷ []

data DHRSectorFunctorialityProofShape : Set where
  objectShape :
    DHRSectorFunctorialityProofShape

  morphismShape :
    DHRSectorFunctorialityProofShape

  transportShape :
    DHRSectorFunctorialityProofShape

  tensorShape :
    DHRSectorFunctorialityProofShape

  reconstructionShape :
    DHRSectorFunctorialityProofShape

canonicalDHRSectorFunctorialityProofShape :
  List DHRSectorFunctorialityProofShape
canonicalDHRSectorFunctorialityProofShape =
  objectShape
  ∷ morphismShape
  ∷ transportShape
  ∷ tensorShape
  ∷ reconstructionShape
  ∷ []

record DHRSectorFunctorialityReceipt : Setω₅ where
  field
    formalismReceipt :
      DHR.DHRFormalismPrimitiveReceipt

    categoryPrimitiveSurface :
      DHR.DHRCategoryPrimitiveSurface

    localisedTransportableEvidence :
      DHR.DHRLocalisedTransportableEndomorphismEvidenceSurface

    gate6LocalizationTransportabilityReceipt :
      DHR.DHRGate6LocalizationTransportabilityAfterLocalAlgebraReceipt

    thermodynamicLimitBoundary :
      DHRLimit.DHRThermodynamicLimitBoundary

    drHypotheses :
      DHR.DRHypothesesForDASHI

    objectLabel :
      String

    objectLabelIsCanonical :
      objectLabel
      ≡
      "objects=localised-transportable-endomorphisms"

    morphismLabel :
      String

    morphismLabelIsCanonical :
      morphismLabel
      ≡
      "morphisms=intertwiners"

    transportLabel :
      String

    transportLabelIsCanonical :
      transportLabel
      ≡
      "transport=compatibility-along-inclusions"

    tensorLabel :
      String

    tensorLabelIsCanonical :
      tensorLabel
      ≡
      "tensor=sector-composition"

    reconstructionLabel :
      String

    reconstructionLabelIsCanonical :
      reconstructionLabel
      ≡
      "reconstruction=colimit-compatible"

    objectFunctorialityRecorded :
      Bool

    objectFunctorialityRecordedIsTrue :
      objectFunctorialityRecorded ≡ true

    morphismFunctorialityRecorded :
      Bool

    morphismFunctorialityRecordedIsTrue :
      morphismFunctorialityRecorded ≡ true

    transportAlongInclusionsRecorded :
      Bool

    transportAlongInclusionsRecordedIsTrue :
      transportAlongInclusionsRecorded ≡ true

    tensorProductLawRecorded :
      Bool

    tensorProductLawRecordedIsTrue :
      tensorProductLawRecorded ≡ true

    reconstructionCompatibilityRecorded :
      Bool

    reconstructionCompatibilityRecordedIsTrue :
      reconstructionCompatibilityRecorded ≡ true

    sectorFunctorialityPromoted :
      Bool

    sectorFunctorialityPromotedIsFalse :
      sectorFunctorialityPromoted ≡ false

    openObligations :
      List DHRSectorFunctorialityOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalDHRSectorFunctorialityOpenObligations

    proofShape :
      List DHRSectorFunctorialityProofShape

    proofShapeIsCanonical :
      proofShape ≡ canonicalDHRSectorFunctorialityProofShape

    boundaryNotes :
      List String

open DHRSectorFunctorialityReceipt public

canonicalDHRSectorFunctorialityReceipt :
  DHRSectorFunctorialityReceipt
canonicalDHRSectorFunctorialityReceipt =
  record
    { formalismReceipt =
        DHR.canonicalDHRFormalismPrimitiveReceipt
    ; categoryPrimitiveSurface =
        DHR.canonicalDHRCategoryPrimitiveSurface
    ; localisedTransportableEvidence =
        DHR.canonicalDHRLocalisedTransportableEndomorphismEvidenceSurface
    ; gate6LocalizationTransportabilityReceipt =
        DHR.canonicalDHRGate6LocalizationTransportabilityAfterLocalAlgebraReceipt
    ; thermodynamicLimitBoundary =
        DHRLimit.canonicalDHRThermodynamicLimitBoundary
    ; drHypotheses =
        DHR.canonicalDRHypothesesForDASHI
    ; objectLabel =
        "objects=localised-transportable-endomorphisms"
    ; objectLabelIsCanonical =
        refl
    ; morphismLabel =
        "morphisms=intertwiners"
    ; morphismLabelIsCanonical =
        refl
    ; transportLabel =
        "transport=compatibility-along-inclusions"
    ; transportLabelIsCanonical =
        refl
    ; tensorLabel =
        "tensor=sector-composition"
    ; tensorLabelIsCanonical =
        refl
    ; reconstructionLabel =
        "reconstruction=colimit-compatible"
    ; reconstructionLabelIsCanonical =
        refl
    ; objectFunctorialityRecorded =
        true
    ; objectFunctorialityRecordedIsTrue =
        refl
    ; morphismFunctorialityRecorded =
        true
    ; morphismFunctorialityRecordedIsTrue =
        refl
    ; transportAlongInclusionsRecorded =
        true
    ; transportAlongInclusionsRecordedIsTrue =
        refl
    ; tensorProductLawRecorded =
        true
    ; tensorProductLawRecordedIsTrue =
        refl
    ; reconstructionCompatibilityRecorded =
        true
    ; reconstructionCompatibilityRecordedIsTrue =
        refl
    ; sectorFunctorialityPromoted =
        false
    ; sectorFunctorialityPromotedIsFalse =
        refl
    ; openObligations =
        canonicalDHRSectorFunctorialityOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; proofShape =
        canonicalDHRSectorFunctorialityProofShape
    ; proofShapeIsCanonical =
        refl
    ; boundaryNotes =
        "The formalism primitive surface already exposes localised endomorphisms, transportables, and intertwiners"
        ∷ "The Gate 6 localization receipt carries the inclusion-compatible transport shape"
        ∷ "The thermodynamic limit boundary supplies the colimit/reconstruction interface"
        ∷ "Tensor composition is recorded as the sector-composition target, not a reconstructed theorem"
        ∷ "No DHR sector functor or Tannaka reconstruction promotion is claimed here"
        ∷ []
    }

canonicalDHRObjectSurface :
  DHR.DHRCategoryPrimitiveSurface
canonicalDHRObjectSurface =
  categoryPrimitiveSurface
    canonicalDHRSectorFunctorialityReceipt

canonicalDHRTransportabilityReceipt :
  DHR.DHRGate6LocalizationTransportabilityAfterLocalAlgebraReceipt
canonicalDHRTransportabilityReceipt =
  gate6LocalizationTransportabilityReceipt
    canonicalDHRSectorFunctorialityReceipt
