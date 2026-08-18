module DASHI.Biology.IntersectionalClaimEvidenceFibreExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.ClaimIndexedEvidencePolarityExact as Indexed
import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Biology.IntersectionalLongitudinalResidualDynamics as Intersectional

------------------------------------------------------------------------
-- Intersectional evidence pooling is claim/context indexed.
--
-- The existing longitudinal carrier keeps body, time, place, relation,
-- institution and axis bundle explicit.  We use that whole carrier as the
-- context index.  Consequently evidence from two distinct situated carriers
-- cannot be merged by mergeSameFibre: an explicit EvidenceFibreAlignment is
-- required first.  This blocks axis/context collapse from manufacturing a
-- contradiction.
------------------------------------------------------------------------

IntersectionalClaimEvidence :
  String →
  Intersectional.IntersectionalResidualCarrier →
  Set
IntersectionalClaimEvidence claim context =
  Indexed.ClaimFibreEvidence
    String
    Intersectional.IntersectionalResidualCarrier
    claim
    context

situatedSupport :
  (claim : String) →
  (context : Intersectional.IntersectionalResidualCarrier) →
  IntersectionalClaimEvidence claim context
situatedSupport claim context =
  Indexed.claimFibreEvidence
    (Four.assess true false)
    (Intersectional.carrierReading context ∷ [])

mergeSituatedEvidence :
  ∀ {claim context} →
  IntersectionalClaimEvidence claim context →
  IntersectionalClaimEvidence claim context →
  IntersectionalClaimEvidence claim context
mergeSituatedEvidence = Indexed.mergeSameFibre

record IntersectionalClaimEvidenceBoundary : Set where
  field
    bodyTimePlaceRelationInstitutionAxesRetained : Bool
    crossContextPoolingAutomaticClaimed : Bool
    axisNeutralContradictionManufactureAllowed : Bool
    explicitAlignmentRequiredAcrossContexts : Bool

canonicalIntersectionalClaimEvidenceBoundary :
  IntersectionalClaimEvidenceBoundary
canonicalIntersectionalClaimEvidenceBoundary = record
  { bodyTimePlaceRelationInstitutionAxesRetained = true
  ; crossContextPoolingAutomaticClaimed = false
  ; axisNeutralContradictionManufactureAllowed = false
  ; explicitAlignmentRequiredAcrossContexts = true
  }
