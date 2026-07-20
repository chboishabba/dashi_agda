module DASHI.Culture.KimmererBraidingAcknowledgement where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Culture.CulturalProvenanceBoundaryCore as Provenance

------------------------------------------------------------------------
-- Formal acknowledgement of Robin Wall Kimmerer's influence.
--
-- DASHI's recurring use of braid, dialectical braid, reciprocal knowledge,
-- provenance-preserving conjunction, and obligation-bearing knowing was
-- materially inspired by Robin Wall Kimmerer's writing, especially Braiding
-- Sweetgrass. "Dialectical braid" is DASHI's own extension and is not
-- attributed to Kimmerer as her terminology.
--
-- This acknowledgement does not claim that DASHI formalises, owns,
-- represents, or substitutes for Indigenous knowledge, Anishinaabe knowledge,
-- Potawatomi knowledge, or living Indigenous practice.

record KimmererBraidingAcknowledgement : Set where
  constructor mkKimmererBraidingAcknowledgement
  field
    author : String
    nationAndProvenance : String
    work : String
    contribution : String
    affectedFormalism : List String
    provenanceBoundary : Provenance.CulturalProvenanceBoundary
    inspirationExplicit : Bool
    dialecticalBraidIsDashiExtension : Bool
    indigenousKnowledgeFormalisedClaim : Bool
    livingPracticeSubstitutedClaim : Bool
    permissionOrCulturalAuthorityClaim : Bool
    extractionBlocked : Bool
    acknowledgementHolds : Bool
    acknowledgementHoldsIsTrue : acknowledgementHolds ≡ true

open KimmererBraidingAcknowledgement public

canonicalKimmererBraidingAcknowledgement : KimmererBraidingAcknowledgement
canonicalKimmererBraidingAcknowledgement =
  mkKimmererBraidingAcknowledgement
    "Robin Wall Kimmerer"
    "Citizen Potawatomi Nation; writings situated in particular scientific, literary, relational, and Indigenous contexts"
    "Braiding Sweetgrass"
    "material inspiration for braided, reciprocal, provenance-preserving and obligation-bearing knowledge formalisms"
    ( "braids of distinct knowledge strands"
    ∷ "DASHI dialectical braids as a later extension"
    ∷ "knowledge strands held together without forced fusion"
    ∷ "reciprocity and obligation"
    ∷ "distinct warrants and provenance"
    ∷ "relation among person community land history and practice"
    ∷ [] )
    Provenance.canonicalCulturalProvenanceBoundary
    true
    true
    false
    false
    false
    true
    true
    refl
