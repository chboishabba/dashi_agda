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
-- Sweetgrass.  This acknowledgement does not claim that DASHI formalises,
-- owns, represents, or substitutes for Indigenous knowledge or living
-- Indigenous practice.

record KimmererBraidingAcknowledgement : Set where
  constructor mkKimmererBraidingAcknowledgement
  field
    author : String
    work : String
    contribution : String
    affectedFormalism : List String
    provenanceBoundary : Provenance.CulturalProvenanceBoundary
    inspirationExplicit : Bool
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
    "Braiding Sweetgrass"
    "inspiration for braided, dialectical, reciprocal, provenance-preserving and obligation-bearing knowledge formalisms"
    ( "dialectical braids"
    ∷ "knowledge strands held together without fusion"
    ∷ "reciprocity and obligation"
    ∷ "distinct warrants and provenance"
    ∷ "relation among person community land and practice"
    ∷ [] )
    Provenance.canonicalCulturalProvenanceBoundary
    true false false false true true refl
