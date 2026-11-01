module DASHI.Culture.CulturalProvenanceBoundaryCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Promotion.AuthorityBoundaryCore as Authority
import DASHI.Promotion.ExplanationAuthorityBoundaryCore as Explanation

------------------------------------------------------------------------
-- Cultural provenance, accountable inspiration, and anti-extraction core.

data ProvenanceKind : Set where
  namedAuthorProvenance : ProvenanceKind
  namedCommunityProvenance : ProvenanceKind
  placePracticeProvenance : ProvenanceKind
  comparativeResearchProvenance : ProvenanceKind
  formalAnalogyProvenance : ProvenanceKind

record ProvenanceRow : Set where
  constructor mkProvenanceRow
  field
    sourceName : String
    provenanceKind : ProvenanceKind
    contribution : String
    limits : String
    permissionOrAuthorityClaimed : Bool
    replaceableByFormalEncoding : Bool

open ProvenanceRow public

record CulturalProvenanceBoundary : Set where
  constructor mkCulturalProvenanceBoundary
  field
    rows : List ProvenanceRow
    explanationBoundary : Explanation.ExplanationAuthorityBoundary
    culturalAuthorityReceipt : Authority.AuthorityBoundaryReceipt
    provenanceRequired : Bool
    noExtraction : Bool
    noSubstitutionForLivingPractice : Bool
    noUniversalisation : Bool
    noRomanticAuthority : Bool
    noEmpiricalCapture : Bool
    formalAnalogyIsLimited : Bool
    boundaryHolds : Bool
    boundaryHoldsIsTrue : boundaryHolds ≡ true

open CulturalProvenanceBoundary public

canonicalCulturalProvenanceBoundary : CulturalProvenanceBoundary
canonicalCulturalProvenanceBoundary =
  mkCulturalProvenanceBoundary
    []
    Explanation.canonicalExplanationAuthorityBoundary
    Authority.canonicalCulturalAuthorityBoundaryReceipt
    true true true true true true true true refl
