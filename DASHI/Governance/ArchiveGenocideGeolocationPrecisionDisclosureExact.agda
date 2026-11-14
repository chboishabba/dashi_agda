module DASHI.Governance.ArchiveGenocideGeolocationPrecisionDisclosureExact where

open import DASHI.Core.Prelude

import DASHI.Governance.ArchiveGenocideGeolocationAntiTargetingExact as Geo

------------------------------------------------------------------------
-- PRECISION REFINEMENT / MINIMUM-SUFFICIENT DISCLOSURE
--
-- This module makes the precision order and preservation obligations explicit.
-- `PrecisionRefines fine coarse` means that the left precision carries at
-- least the location detail of the right.  It does NOT grant authority to
-- disclose the finer observation.
------------------------------------------------------------------------

data PrecisionRefines :
    Geo.LocationPrecision → Geo.LocationPrecision → Set where
  precisionRefl :
    ∀ {precision} → PrecisionRefines precision precision
  neighbourhoodRefinesTown :
    PrecisionRefines Geo.neighbourhoodOrCamp Geo.townOrCity
  buildingRefinesNeighbourhood :
    PrecisionRefines Geo.buildingOrFacility Geo.neighbourhoodOrCamp
  exactRefinesBuilding :
    PrecisionRefines Geo.exactCoordinate Geo.buildingOrFacility
  buildingRefinesTown :
    PrecisionRefines Geo.buildingOrFacility Geo.townOrCity
  exactRefinesNeighbourhood :
    PrecisionRefines Geo.exactCoordinate Geo.neighbourhoodOrCamp
  exactRefinesTown :
    PrecisionRefines Geo.exactCoordinate Geo.townOrCity

precisionRefinesTrans :
  ∀ {fine middle coarse} →
  PrecisionRefines fine middle →
  PrecisionRefines middle coarse →
  PrecisionRefines fine coarse
precisionRefinesTrans precisionRefl right = right
precisionRefinesTrans neighbourhoodRefinesTown precisionRefl =
  neighbourhoodRefinesTown
precisionRefinesTrans buildingRefinesNeighbourhood precisionRefl =
  buildingRefinesNeighbourhood
precisionRefinesTrans buildingRefinesNeighbourhood neighbourhoodRefinesTown =
  buildingRefinesTown
precisionRefinesTrans exactRefinesBuilding precisionRefl = exactRefinesBuilding
precisionRefinesTrans exactRefinesBuilding buildingRefinesNeighbourhood =
  exactRefinesNeighbourhood
precisionRefinesTrans exactRefinesBuilding buildingRefinesTown = exactRefinesTown
precisionRefinesTrans buildingRefinesTown precisionRefl = buildingRefinesTown
precisionRefinesTrans exactRefinesNeighbourhood precisionRefl =
  exactRefinesNeighbourhood
precisionRefinesTrans exactRefinesNeighbourhood neighbourhoodRefinesTown =
  exactRefinesTown
precisionRefinesTrans exactRefinesTown precisionRefl = exactRefinesTown

------------------------------------------------------------------------
-- A disclosure view carries only a bounded location surface but retains the
-- evidence lineage needed to audit where that surface came from.
------------------------------------------------------------------------

record DisclosureView : Set where
  constructor disclosure-view
  field
    disclosedPlace : Geo.CoarsePlace
    disclosedPrecision : Geo.LocationPrecision
    originalPrecision : Geo.LocationPrecision
    precisionWasMinimised :
      PrecisionRefines originalPrecision disclosedPrecision
    provenanceReference : String
    origin : Geo.GeolocationOrigin
    reviewState : Geo.GeolocationReviewState
    eventTimeBasis : Geo.EventTimeBasis
    corroborationReference : String

open DisclosureView public

minimumNeighbourhoodDisclosure :
  (evidence : Geo.GeolocationEvidence) →
  PrecisionRefines
    (Geo.statedPrecision evidence)
    Geo.neighbourhoodOrCamp →
  DisclosureView
minimumNeighbourhoodDisclosure evidence refinement =
  disclosure-view
    (Geo.coarseEvidencePlace evidence)
    Geo.neighbourhoodOrCamp
    (Geo.statedPrecision evidence)
    refinement
    (Geo.provenanceReference evidence)
    (Geo.origin evidence)
    (Geo.reviewState evidence)
    (Geo.eventTimeBasis evidence)
    (Geo.corroborationReference evidence)

provenanceSurvivesMinimumDisclosure :
  ∀ (evidence : Geo.GeolocationEvidence)
    (refinement :
      PrecisionRefines
        (Geo.statedPrecision evidence)
        Geo.neighbourhoodOrCamp) →
  provenanceReference (minimumNeighbourhoodDisclosure evidence refinement)
    ≡ Geo.provenanceReference evidence
provenanceSurvivesMinimumDisclosure evidence refinement = refl

originSurvivesMinimumDisclosure :
  ∀ (evidence : Geo.GeolocationEvidence)
    (refinement :
      PrecisionRefines
        (Geo.statedPrecision evidence)
        Geo.neighbourhoodOrCamp) →
  origin (minimumNeighbourhoodDisclosure evidence refinement)
    ≡ Geo.origin evidence
originSurvivesMinimumDisclosure evidence refinement = refl

reviewStateSurvivesMinimumDisclosure :
  ∀ (evidence : Geo.GeolocationEvidence)
    (refinement :
      PrecisionRefines
        (Geo.statedPrecision evidence)
        Geo.neighbourhoodOrCamp) →
  reviewState (minimumNeighbourhoodDisclosure evidence refinement)
    ≡ Geo.reviewState evidence
reviewStateSurvivesMinimumDisclosure evidence refinement = refl

eventTimeBasisSurvivesMinimumDisclosure :
  ∀ (evidence : Geo.GeolocationEvidence)
    (refinement :
      PrecisionRefines
        (Geo.statedPrecision evidence)
        Geo.neighbourhoodOrCamp) →
  eventTimeBasis (minimumNeighbourhoodDisclosure evidence refinement)
    ≡ Geo.eventTimeBasis evidence
eventTimeBasisSurvivesMinimumDisclosure evidence refinement = refl

corroborationSurvivesMinimumDisclosure :
  ∀ (evidence : Geo.GeolocationEvidence)
    (refinement :
      PrecisionRefines
        (Geo.statedPrecision evidence)
        Geo.neighbourhoodOrCamp) →
  corroborationReference
      (minimumNeighbourhoodDisclosure evidence refinement)
    ≡ Geo.corroborationReference evidence
corroborationSurvivesMinimumDisclosure evidence refinement = refl

------------------------------------------------------------------------
-- Independent coordinates / anti-promotion witnesses.
------------------------------------------------------------------------

reviewedExact : Geo.GeolocationReviewState × Geo.LocationPrecision
reviewedExact = Geo.reviewed , Geo.exactCoordinate

reviewedTown : Geo.GeolocationReviewState × Geo.LocationPrecision
reviewedTown = Geo.reviewed , Geo.townOrCity

sameReviewDifferentPrecision :
  proj₁ reviewedExact ≡ proj₁ reviewedTown
sameReviewDifferentPrecision = refl

reviewedExactPrecisionDiffersFromReviewedTown :
  proj₂ reviewedExact ≡ proj₂ reviewedTown → ⊥
reviewedExactPrecisionDiffersFromReviewedTown ()

thirdPartyReviewed : Geo.GeolocationOrigin × Geo.GeolocationReviewState
thirdPartyReviewed = Geo.independentThirdPartyOSINT , Geo.reviewed

archiveReviewed : Geo.GeolocationOrigin × Geo.GeolocationReviewState
archiveReviewed = Geo.archiveResolved , Geo.reviewed

sameReviewDifferentOrigin :
  proj₂ thirdPartyReviewed ≡ proj₂ archiveReviewed
sameReviewDifferentOrigin = refl

thirdPartyOriginRemainsDistinct :
  proj₁ thirdPartyReviewed ≡ proj₁ archiveReviewed → ⊥
thirdPartyOriginRemainsDistinct ()

------------------------------------------------------------------------
-- Terminal boundary.
------------------------------------------------------------------------

record PrecisionDisclosureBoundary : Set where
  constructor precision-disclosure-boundary
  field
    precisionFormsExplicitRefinementOrder : Bool
    precisionFormsExplicitRefinementOrderIsTrue :
      precisionFormsExplicitRefinementOrder ≡ true

    refinementGrantsDisclosureAuthority : Bool
    refinementGrantsDisclosureAuthorityIsFalse :
      refinementGrantsDisclosureAuthority ≡ false

    minimumDisclosurePreservesProvenance : Bool
    minimumDisclosurePreservesProvenanceIsTrue :
      minimumDisclosurePreservesProvenance ≡ true

    minimumDisclosurePreservesOrigin : Bool
    minimumDisclosurePreservesOriginIsTrue :
      minimumDisclosurePreservesOrigin ≡ true

    minimumDisclosurePreservesReviewState : Bool
    minimumDisclosurePreservesReviewStateIsTrue :
      minimumDisclosurePreservesReviewState ≡ true

    minimumDisclosurePreservesEventTimeBasis : Bool
    minimumDisclosurePreservesEventTimeBasisIsTrue :
      minimumDisclosurePreservesEventTimeBasis ≡ true

    reviewStateDeterminesPrecision : Bool
    reviewStateDeterminesPrecisionIsFalse :
      reviewStateDeterminesPrecision ≡ false

    reviewStateDeterminesOrigin : Bool
    reviewStateDeterminesOriginIsFalse :
      reviewStateDeterminesOrigin ≡ false

open PrecisionDisclosureBoundary public

canonicalPrecisionDisclosureBoundary : PrecisionDisclosureBoundary
canonicalPrecisionDisclosureBoundary =
  precision-disclosure-boundary
    true refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
