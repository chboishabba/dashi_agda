module DASHI.Physics.Closure.SpacetimeLatticeFromCarrierDepthReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierLatticeYMDefinitionReceipt as Lattice

data SpacetimeLatticeFromCarrierDepthStatus : Set where
  spacetimeLatticeDepthCandidateRecordedNoClayPromotion :
    SpacetimeLatticeFromCarrierDepthStatus

data SpacetimeLatticeChoice : Set where
  primeLanesAsSpatialDirections :
    SpacetimeLatticeChoice

  depthAsEuclideanTime :
    SpacetimeLatticeChoice

  threeSitesPerTimeSlice :
    SpacetimeLatticeChoice

  continuumSpatialRefinementStillOpen :
    SpacetimeLatticeChoice

canonicalSpacetimeLatticeChoices : List SpacetimeLatticeChoice
canonicalSpacetimeLatticeChoices =
  primeLanesAsSpatialDirections
  ∷ depthAsEuclideanTime
  ∷ threeSitesPerTimeSlice
  ∷ continuumSpatialRefinementStillOpen
  ∷ []

data SpacetimeLatticeDepthBlocker : Set where
  missingDepthToSpacingLaw :
    SpacetimeLatticeDepthBlocker

  missingSpatialContinuumRefinement :
    SpacetimeLatticeDepthBlocker

  missingEuclideanReflectionStructure :
    SpacetimeLatticeDepthBlocker

  missingContinuumLimit :
    SpacetimeLatticeDepthBlocker

canonicalSpacetimeLatticeDepthBlockers :
  List SpacetimeLatticeDepthBlocker
canonicalSpacetimeLatticeDepthBlockers =
  missingDepthToSpacingLaw
  ∷ missingSpatialContinuumRefinement
  ∷ missingEuclideanReflectionStructure
  ∷ missingContinuumLimit
  ∷ []

data SpacetimeLatticeDepthPromotion : Set where

spacetimeLatticeDepthPromotionImpossibleHere :
  SpacetimeLatticeDepthPromotion →
  ⊥
spacetimeLatticeDepthPromotionImpossibleHere ()

record SpacetimeLatticeFromCarrierDepthReceipt : Setω where
  field
    status :
      SpacetimeLatticeFromCarrierDepthStatus

    carrierLatticeReceipt :
      Lattice.CarrierLatticeYMDefinitionReceipt

    carrierSpatialSiteCountThree :
      Lattice.spatialSiteCount carrierLatticeReceipt ≡ 3

    euclideanTimeFromDepth :
      Bool

    euclideanTimeFromDepthIsCandidateTrue :
      euclideanTimeFromDepth ≡ true

    spatialDirectionsFromPrimeLanes :
      Bool

    spatialDirectionsFromPrimeLanesIsCandidateTrue :
      spatialDirectionsFromPrimeLanes ≡ true

    timeSliceSiteCount :
      Nat

    timeSliceSiteCountIsThree :
      timeSliceSiteCount ≡ 3

    lattice4DFromCarrierProved :
      Bool

    lattice4DFromCarrierProvedIsFalse :
      lattice4DFromCarrierProved ≡ false

    choices :
      List SpacetimeLatticeChoice

    choicesAreCanonical :
      choices ≡ canonicalSpacetimeLatticeChoices

    spacetimeLatticeCandidateRecorded :
      Bool

    spacetimeLatticeCandidateRecordedIsTrue :
      spacetimeLatticeCandidateRecorded ≡ true

    continuumLimitConstructed :
      Bool

    continuumLimitConstructedIsFalse :
      continuumLimitConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    blockers :
      List SpacetimeLatticeDepthBlocker

    blockersAreCanonical :
      blockers ≡ canonicalSpacetimeLatticeDepthBlockers

    promotionFlags :
      List SpacetimeLatticeDepthPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open SpacetimeLatticeFromCarrierDepthReceipt public

canonicalSpacetimeLatticeFromCarrierDepthReceipt :
  SpacetimeLatticeFromCarrierDepthReceipt
canonicalSpacetimeLatticeFromCarrierDepthReceipt =
  record
    { status =
        spacetimeLatticeDepthCandidateRecordedNoClayPromotion
    ; carrierLatticeReceipt =
        Lattice.canonicalCarrierLatticeYMDefinitionReceipt
    ; carrierSpatialSiteCountThree =
        refl
    ; euclideanTimeFromDepth =
        true
    ; euclideanTimeFromDepthIsCandidateTrue =
        refl
    ; spatialDirectionsFromPrimeLanes =
        true
    ; spatialDirectionsFromPrimeLanesIsCandidateTrue =
        refl
    ; timeSliceSiteCount =
        3
    ; timeSliceSiteCountIsThree =
        refl
    ; lattice4DFromCarrierProved =
        false
    ; lattice4DFromCarrierProvedIsFalse =
        refl
    ; choices =
        canonicalSpacetimeLatticeChoices
    ; choicesAreCanonical =
        refl
    ; spacetimeLatticeCandidateRecorded =
        true
    ; spacetimeLatticeCandidateRecordedIsTrue =
        refl
    ; continuumLimitConstructed =
        false
    ; continuumLimitConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; blockers =
        canonicalSpacetimeLatticeDepthBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "B2 records depth as a candidate Euclidean time direction and prime lanes as spatial directions"
        ∷ "The construction is a regulator roadmap, not a proved 3+1 continuum spacetime"
        ∷ "No Clay Yang-Mills or terminal Clay claim is promoted"
        ∷ []
    }

spacetimeLatticeDepthDoesNotPromoteClay :
  clayYangMillsPromoted canonicalSpacetimeLatticeFromCarrierDepthReceipt
  ≡
  false
spacetimeLatticeDepthDoesNotPromoteClay =
  refl
