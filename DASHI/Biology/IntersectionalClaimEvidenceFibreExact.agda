module DASHI.Biology.IntersectionalClaimEvidenceFibreExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.ClaimIndexedEvidencePolarityExact as Indexed
import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Biology.IntersectionalLongitudinalResidualDynamics as Intersectional

------------------------------------------------------------------------
-- Intersectional evidence pooling is claim/context/operator indexed.
--
-- The existing longitudinal carrier keeps body, time, place, relation,
-- institution and axis bundle explicit.  The opposition descriptor separately
-- keeps the base claim, opposing target and operator role explicit.  Thus two
-- reports cannot manufacture a contradiction merely by sharing a surface label
-- while differing in situated context OR in what kind of opposition is meant.
------------------------------------------------------------------------

IntersectionalClaimEvidence :
  Indexed.OppositionDescriptor String →
  Intersectional.IntersectionalResidualCarrier →
  Set
IntersectionalClaimEvidence opposition context =
  Indexed.ClaimFibreEvidence
    String
    Intersectional.IntersectionalResidualCarrier
    opposition
    context

situatedSupport :
  (opposition : Indexed.OppositionDescriptor String) →
  (context : Intersectional.IntersectionalResidualCarrier) →
  IntersectionalClaimEvidence opposition context
situatedSupport opposition context =
  Indexed.claimFibreEvidence
    (Four.assess true false)
    (Intersectional.carrierReading context ∷ [])

mergeSituatedEvidence :
  ∀ {opposition context} →
  IntersectionalClaimEvidence opposition context →
  IntersectionalClaimEvidence opposition context →
  IntersectionalClaimEvidence opposition context
mergeSituatedEvidence = Indexed.mergeSameFibre

record IntersectionalClaimEvidenceBoundary : Set where
  field
    bodyTimePlaceRelationInstitutionAxesRetained : Bool
    crossContextPoolingAutomaticClaimed : Bool
    crossOppositionRolePoolingAutomaticClaimed : Bool
    axisNeutralContradictionManufactureAllowed : Bool
    explicitAlignmentRequiredAcrossContexts : Bool

canonicalIntersectionalClaimEvidenceBoundary :
  IntersectionalClaimEvidenceBoundary
canonicalIntersectionalClaimEvidenceBoundary = record
  { bodyTimePlaceRelationInstitutionAxesRetained = true
  ; crossContextPoolingAutomaticClaimed = false
  ; crossOppositionRolePoolingAutomaticClaimed = false
  ; axisNeutralContradictionManufactureAllowed = false
  ; explicitAlignmentRequiredAcrossContexts = true
  }
