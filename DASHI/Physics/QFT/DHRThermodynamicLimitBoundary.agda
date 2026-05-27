module DASHI.Physics.QFT.DHRThermodynamicLimitBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- DHR thermodynamic / inductive limit boundary surface.
--
-- This module records the directed-system shape of the thermodynamic limit
-- lane: depth inclusions, a colimit object, universal property data, and the
-- DHR sector-transport compatibility boundary.  It reuses the repo's
-- existing colimit universality target and DHR decomposition witness, but it
-- does not claim a full infinite-volume QFT limit promotion.

data DHRThermodynamicLimitStatus : Set where
  boundaryOnlyNoPromotion :
    DHRThermodynamicLimitStatus

data DHRThermodynamicLimitOpenObligation : Set where
  missingDepthEmbeddingFunctoriality :
    DHRThermodynamicLimitOpenObligation

  missingLocalityPreservation :
    DHRThermodynamicLimitOpenObligation

  missingColimitFactorization :
    DHRThermodynamicLimitOpenObligation

  missingSectorTransportStability :
    DHRThermodynamicLimitOpenObligation

  missingReconstructionCompatibility :
    DHRThermodynamicLimitOpenObligation

canonicalDHRThermodynamicLimitOpenObligations :
  List DHRThermodynamicLimitOpenObligation
canonicalDHRThermodynamicLimitOpenObligations =
  missingDepthEmbeddingFunctoriality
  ∷ missingLocalityPreservation
  ∷ missingColimitFactorization
  ∷ missingSectorTransportStability
  ∷ missingReconstructionCompatibility
  ∷ []

data DHRThermodynamicLimitProofShape : Set where
  functorialDepthInclusions :
    DHRThermodynamicLimitProofShape

  localityPreservation :
    DHRThermodynamicLimitProofShape

  colimitFactorization :
    DHRThermodynamicLimitProofShape

  sectorTransportStability :
    DHRThermodynamicLimitProofShape

  reconstructionCompatibility :
    DHRThermodynamicLimitProofShape

canonicalDHRThermodynamicLimitProofShape :
  List DHRThermodynamicLimitProofShape
canonicalDHRThermodynamicLimitProofShape =
  functorialDepthInclusions
  ∷ localityPreservation
  ∷ colimitFactorization
  ∷ sectorTransportStability
  ∷ reconstructionCompatibility
  ∷ []

record DHRThermodynamicLimitBoundaryReceipt : Setω where
  field
    colimitUniversalityReceiptLabel :
      String

    colimitUniversalityReceiptRecorded :
      Bool

    colimitUniversalityReceiptRecordedIsTrue :
      colimitUniversalityReceiptRecorded ≡ true

    dhrSectorDecompositionLabel :
      String

    dhrSectorDecompositionReceiptRecorded :
      Bool

    dhrSectorDecompositionReceiptRecordedIsTrue :
      dhrSectorDecompositionReceiptRecorded ≡ true

    depthEmbeddingFunctorialityTarget :
      Bool

    depthEmbeddingFunctorialityTargetIsTrue :
      depthEmbeddingFunctorialityTarget ≡ true

    localityPreservationTarget :
      Bool

    localityPreservationTargetIsTrue :
      localityPreservationTarget ≡ true

    colimitFactorizationTarget :
      Bool

    colimitFactorizationTargetIsTrue :
      colimitFactorizationTarget ≡ true

    sectorTransportStabilityTarget :
      Bool

    sectorTransportStabilityTargetIsTrue :
      sectorTransportStabilityTarget ≡ true

    reconstructionCompatibilityTarget :
      Bool

    reconstructionCompatibilityTargetIsTrue :
      reconstructionCompatibilityTarget ≡ true

    thermodynamicLimitPromoted :
      Bool

    thermodynamicLimitPromotedIsFalse :
      thermodynamicLimitPromoted ≡ false

    openObligations :
      List DHRThermodynamicLimitOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalDHRThermodynamicLimitOpenObligations

    proofShape :
      List DHRThermodynamicLimitProofShape

    proofShapeIsCanonical :
      proofShape ≡ canonicalDHRThermodynamicLimitProofShape

    boundaryNotes :
      List String

open DHRThermodynamicLimitBoundaryReceipt public

canonicalDHRThermodynamicLimitBoundaryReceipt :
  DHRThermodynamicLimitBoundaryReceipt
canonicalDHRThermodynamicLimitBoundaryReceipt =
  record
    { colimitUniversalityReceiptLabel =
        "AQFT colimit universality receipt target"
    ; colimitUniversalityReceiptRecorded =
        true
    ; colimitUniversalityReceiptRecordedIsTrue =
        refl
    ; dhrSectorDecompositionLabel =
        "DHR sector decomposition receipt target"
    ; dhrSectorDecompositionReceiptRecorded =
        true
    ; dhrSectorDecompositionReceiptRecordedIsTrue =
        refl
    ; depthEmbeddingFunctorialityTarget =
        true
    ; depthEmbeddingFunctorialityTargetIsTrue =
        refl
    ; localityPreservationTarget =
        true
    ; localityPreservationTargetIsTrue =
        refl
    ; colimitFactorizationTarget =
        true
    ; colimitFactorizationTargetIsTrue =
        refl
    ; sectorTransportStabilityTarget =
        true
    ; sectorTransportStabilityTargetIsTrue =
        refl
    ; reconstructionCompatibilityTarget =
        true
    ; reconstructionCompatibilityTargetIsTrue =
        refl
    ; thermodynamicLimitPromoted =
        false
    ; thermodynamicLimitPromotedIsFalse =
        refl
    ; openObligations =
        canonicalDHRThermodynamicLimitOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; proofShape =
        canonicalDHRThermodynamicLimitProofShape
    ; proofShapeIsCanonical =
        refl
    ; boundaryNotes =
        "The AQFT colimit universality receipt is reused as the external anchor"
        ∷ "The DHR sector decomposition is threaded through as the compatibility witness"
        ∷ "Depth embeddings are named as a functorial inclusion target, not a promoted theorem"
        ∷ "The thermodynamic/infinite-volume limit remains boundary-only and fail-closed"
        ∷ []
    }

dhrThermodynamicLimitFirstOpenObligation :
  DHRThermodynamicLimitOpenObligation
dhrThermodynamicLimitFirstOpenObligation =
  missingDepthEmbeddingFunctoriality
