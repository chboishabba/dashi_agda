module DASHI.Promotion.ExplanationAuthorityBoundaryCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Promotion.AuthorityBoundaryCore as Authority

------------------------------------------------------------------------
-- Shared explanation / proof / authority boundary.
--
-- Narrative, metaphor, intuition, typed structure, empirical support, and
-- institutional authority are distinct routes.  This core refines the
-- repository-wide AuthorityBoundaryCore rather than defining a parallel
-- authority vocabulary.

data ExplanationRoute : Set where
  narrativeGuideRoute : ExplanationRoute
  metaphorRoute : ExplanationRoute
  phenomenologicalDescriptionRoute : ExplanationRoute
  typedStructureRoute : ExplanationRoute
  empiricalSupportRoute : ExplanationRoute
  institutionalAuthorityRoute : ExplanationRoute

data ExplanationStatus : Set where
  guideOnlyStatus : ExplanationStatus
  structureOnlyStatus : ExplanationStatus
  supportRequiredStatus : ExplanationStatus
  authorityExternallyRequiredStatus : ExplanationStatus

record ExplanationBoundaryRow : Set where
  constructor mkExplanationBoundaryRow
  field
    rowLabel : String
    rowRoute : ExplanationRoute
    rowStatus : ExplanationStatus
    mayGuide : Bool
    isTypedProof : Bool
    isEmpiricalSupport : Bool
    isInstitutionalAuthority : Bool

open ExplanationBoundaryRow public

canonicalExplanationRows : List ExplanationBoundaryRow
canonicalExplanationRows =
  mkExplanationBoundaryRow "narrative guide" narrativeGuideRoute guideOnlyStatus true false false false
  ∷ mkExplanationBoundaryRow "metaphor" metaphorRoute guideOnlyStatus true false false false
  ∷ mkExplanationBoundaryRow "phenomenological description" phenomenologicalDescriptionRoute guideOnlyStatus true false false false
  ∷ mkExplanationBoundaryRow "typed structure" typedStructureRoute structureOnlyStatus true true false false
  ∷ mkExplanationBoundaryRow "empirical support" empiricalSupportRoute supportRequiredStatus false false true false
  ∷ mkExplanationBoundaryRow "institutional authority" institutionalAuthorityRoute authorityExternallyRequiredStatus false false false true
  ∷ []

record ExplanationAuthorityBoundary : Set where
  constructor mkExplanationAuthorityBoundary
  field
    rows : List ExplanationBoundaryRow
    culturalAuthorityReceipt : Authority.AuthorityBoundaryReceipt
    clinicalAuthorityReceipt : Authority.AuthorityBoundaryReceipt
    legalAuthorityReceipt : Authority.AuthorityBoundaryReceipt
    narrativeIsNotProof : Bool
    typedStructureIsNotEmpiricalSupport : Bool
    empiricalSupportIsNotInstitutionalAuthority : Bool
    noRoutePromotedByVocabularyAlone : Bool
    boundaryHolds : Bool
    boundaryHoldsIsTrue : boundaryHolds ≡ true

open ExplanationAuthorityBoundary public

canonicalExplanationAuthorityBoundary : ExplanationAuthorityBoundary
canonicalExplanationAuthorityBoundary =
  mkExplanationAuthorityBoundary
    canonicalExplanationRows
    Authority.canonicalCulturalAuthorityBoundaryReceipt
    Authority.canonicalClinicalAuthorityBoundaryReceipt
    Authority.canonicalLegalAuthorityBoundaryReceipt
    true true true true true refl
