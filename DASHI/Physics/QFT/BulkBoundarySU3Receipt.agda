module DASHI.Physics.QFT.BulkBoundarySU3Receipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.ColourFromPrimeLaneExtensionReceipt as Colour
import DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt as Conditional

------------------------------------------------------------------------
-- Bulk/boundary SU(3) receipt.
--
-- This receipt records a deliberately conditional holographic diagnostic:
-- SU(3)_1 Chern-Simons is treated as a 2+1D boundary candidate for a 3+1D
-- topological/gauge bulk.  The bulk SU(3) gauge-group reading is conditional
-- on a supplied Chern-Simons identification, and no exact SU(3)_c or exact
-- G_DHR ~= G_SM promotion is claimed.

data BulkBoundarySU3Status : Set where
  su3OneChernSimonsBoundaryCandidate :
    BulkBoundarySU3Status

data BulkGaugeGroupSU3Status : Set where
  conditionalOnChernSimonsIdentification :
    BulkGaugeGroupSU3Status

data HolographicPrincipleCarrierStatus : Set where
  candidate :
    HolographicPrincipleCarrierStatus

data BulkBoundarySU3Residual : Set where
  missingChernSimonsIdentification :
    BulkBoundarySU3Residual

  missingThreePlusOneDimensionalBulkConstruction :
    BulkBoundarySU3Residual

  missingBoundaryBulkFunctor :
    BulkBoundarySU3Residual

  missingExactColourGaugePromotion :
    BulkBoundarySU3Residual

  missingExactGDHREqualsGSMIdentification :
    BulkBoundarySU3Residual

canonicalBulkBoundarySU3Residuals :
  List BulkBoundarySU3Residual
canonicalBulkBoundarySU3Residuals =
  missingChernSimonsIdentification
  ∷ missingThreePlusOneDimensionalBulkConstruction
  ∷ missingBoundaryBulkFunctor
  ∷ missingExactColourGaugePromotion
  ∷ missingExactGDHREqualsGSMIdentification
  ∷ []

su3OneChernSimonsBoundaryLabel : String
su3OneChernSimonsBoundaryLabel =
  "SU(3)_1 Chern-Simons 2+1D boundary candidate"

bulkTopologicalGaugeCandidateLabel : String
bulkTopologicalGaugeCandidateLabel =
  "3+1D topological/gauge bulk candidate"

bulkGaugeGroupConditionalLabel : String
bulkGaugeGroupConditionalLabel =
  "bulk gauge group SU(3) is conditional on identifying the boundary as SU(3)_1 Chern-Simons"

record BulkBoundarySU3Receipt : Setω where
  field
    status :
      BulkBoundarySU3Status

    boundaryTheory :
      String

    boundaryTheoryIsSU3OneChernSimons :
      boundaryTheory ≡ su3OneChernSimonsBoundaryLabel

    boundaryDimension :
      String

    boundaryDimensionIsTwoPlusOne :
      boundaryDimension ≡ "2+1D"

    bulkCandidate :
      String

    bulkCandidateIsThreePlusOneTopologicalGauge :
      bulkCandidate ≡ bulkTopologicalGaugeCandidateLabel

    bulkDimension :
      String

    bulkDimensionIsThreePlusOne :
      bulkDimension ≡ "3+1D"

    holographicSU3Candidate :
      Bool

    holographicSU3CandidateIsTrue :
      holographicSU3Candidate ≡ true

    bulkGaugeGroupSU3 :
      BulkGaugeGroupSU3Status

    bulkGaugeGroupSU3IsConditionalOnCSIdentification :
      bulkGaugeGroupSU3 ≡ conditionalOnChernSimonsIdentification

    bulkGaugeGroupSU3ConditionalBoundary :
      String

    bulkGaugeGroupSU3ConditionalBoundaryIsCanonical :
      bulkGaugeGroupSU3ConditionalBoundary ≡ bulkGaugeGroupConditionalLabel

    holographicPrincipleInCarrier :
      HolographicPrincipleCarrierStatus

    holographicPrincipleInCarrierIsCandidate :
      holographicPrincipleInCarrier ≡ candidate

    exactSU3c :
      Bool

    exactSU3cIsFalse :
      exactSU3c ≡ false

    exactGDHREqualsGSM :
      Bool

    exactGDHREqualsGSMIsFalse :
      exactGDHREqualsGSM ≡ false

    colourExtensionReceipt :
      Colour.ColourFromPrimeLaneExtensionReceipt

    existingFullSU3FromPermutationIsFalse :
      Colour.ColourFromPrimeLaneExtensionReceipt.fullSU3FromPermutation
        colourExtensionReceipt
      ≡
      false

    conditionalGDHRSMPromotionReceipt :
      Conditional.ConditionalGDHRSMPromotionReceipt

    existingUnconditionalGDHREqualsGSMIsFalse :
      Conditional.ConditionalGDHRSMPromotionReceipt.unconditionalGDHREqualsGSMPromoted
        conditionalGDHRSMPromotionReceipt
      ≡
      false

    residuals :
      List BulkBoundarySU3Residual

    residualsAreCanonical :
      residuals ≡ canonicalBulkBoundarySU3Residuals

    receiptBoundary :
      List String

open BulkBoundarySU3Receipt public

canonicalBulkBoundarySU3Receipt :
  BulkBoundarySU3Receipt
canonicalBulkBoundarySU3Receipt =
  record
    { status =
        su3OneChernSimonsBoundaryCandidate
    ; boundaryTheory =
        su3OneChernSimonsBoundaryLabel
    ; boundaryTheoryIsSU3OneChernSimons =
        refl
    ; boundaryDimension =
        "2+1D"
    ; boundaryDimensionIsTwoPlusOne =
        refl
    ; bulkCandidate =
        bulkTopologicalGaugeCandidateLabel
    ; bulkCandidateIsThreePlusOneTopologicalGauge =
        refl
    ; bulkDimension =
        "3+1D"
    ; bulkDimensionIsThreePlusOne =
        refl
    ; holographicSU3Candidate =
        true
    ; holographicSU3CandidateIsTrue =
        refl
    ; bulkGaugeGroupSU3 =
        conditionalOnChernSimonsIdentification
    ; bulkGaugeGroupSU3IsConditionalOnCSIdentification =
        refl
    ; bulkGaugeGroupSU3ConditionalBoundary =
        bulkGaugeGroupConditionalLabel
    ; bulkGaugeGroupSU3ConditionalBoundaryIsCanonical =
        refl
    ; holographicPrincipleInCarrier =
        candidate
    ; holographicPrincipleInCarrierIsCandidate =
        refl
    ; exactSU3c =
        false
    ; exactSU3cIsFalse =
        refl
    ; exactGDHREqualsGSM =
        false
    ; exactGDHREqualsGSMIsFalse =
        refl
    ; colourExtensionReceipt =
        Colour.canonicalColourFromPrimeLaneExtensionReceipt
    ; existingFullSU3FromPermutationIsFalse =
        refl
    ; conditionalGDHRSMPromotionReceipt =
        Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; existingUnconditionalGDHREqualsGSMIsFalse =
        refl
    ; residuals =
        canonicalBulkBoundarySU3Residuals
    ; residualsAreCanonical =
        refl
    ; receiptBoundary =
        "SU(3)_1 Chern-Simons is recorded only as a 2+1D boundary candidate"
        ∷ "The associated 3+1D topological/gauge bulk is a candidate carrier-side holographic diagnostic"
        ∷ "bulkGaugeGroupSU3 is conditional on a supplied Chern-Simons identification"
        ∷ "No exact SU(3)_c colour gauge group or exact G_DHR ~= G_SM identification is promoted"
        ∷ []
    }

bulkBoundaryHolographicSU3CandidateIsTrue :
  holographicSU3Candidate canonicalBulkBoundarySU3Receipt
  ≡
  true
bulkBoundaryHolographicSU3CandidateIsTrue =
  refl

bulkBoundaryBulkGaugeGroupSU3IsConditional :
  bulkGaugeGroupSU3 canonicalBulkBoundarySU3Receipt
  ≡
  conditionalOnChernSimonsIdentification
bulkBoundaryBulkGaugeGroupSU3IsConditional =
  refl

bulkBoundaryHolographicPrincipleInCarrierIsCandidate :
  holographicPrincipleInCarrier canonicalBulkBoundarySU3Receipt
  ≡
  candidate
bulkBoundaryHolographicPrincipleInCarrierIsCandidate =
  refl

bulkBoundaryExactSU3cIsFalse :
  exactSU3c canonicalBulkBoundarySU3Receipt
  ≡
  false
bulkBoundaryExactSU3cIsFalse =
  refl

bulkBoundaryExactGDHREqualsGSMIsFalse :
  exactGDHREqualsGSM canonicalBulkBoundarySU3Receipt
  ≡
  false
bulkBoundaryExactGDHREqualsGSMIsFalse =
  refl
