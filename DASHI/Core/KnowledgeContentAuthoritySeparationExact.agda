module DASHI.Core.KnowledgeContentAuthoritySeparationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- KNOWLEDGE CONTENT / PRACTICE / AUTHORITY SEPARATION
--
-- Knowing a technique, being able to perform it, and holding authority to
-- authorize it for a situated place/community are independent coordinates.
------------------------------------------------------------------------

record SituatedKnowledgeAuthority (Agent Place Content : Set) : Set₁ where
  constructor situatedKnowledgeAuthority
  field
    Knows : Agent → Content → Set
    CanPractice : Agent → Place → Content → Set
    CanAuthorize : Agent → Place → Content → Set

open SituatedKnowledgeAuthority public

record ContentWithoutAuthority
    {Agent Place Content : Set}
    (system : SituatedKnowledgeAuthority Agent Place Content) : Set where
  constructor contentWithoutAuthority
  field
    agent : Agent
    place : Place
    content : Content
    knows : Knows system agent content
    cannotAuthorize : CanAuthorize system agent place content → ⊥

record PracticeWithoutAuthority
    {Agent Place Content : Set}
    (system : SituatedKnowledgeAuthority Agent Place Content) : Set where
  constructor practiceWithoutAuthority
  field
    agent : Agent
    place : Place
    content : Content
    canPractice : CanPractice system agent place content
    cannotAuthorize : CanAuthorize system agent place content → ⊥

record KnowledgeAuthorityBoundary : Set where
  constructor knowledgeAuthorityBoundary
  field
    knowingTechniqueImpliesSituatedAuthority : Bool
    knowingTechniqueImpliesSituatedAuthorityIsFalse : knowingTechniqueImpliesSituatedAuthority ≡ false
    practicalCompetenceImpliesAuthorization : Bool
    practicalCompetenceImpliesAuthorizationIsFalse : practicalCompetenceImpliesAuthorization ≡ false
    externalDocumentationCreatesCommunityAuthority : Bool
    externalDocumentationCreatesCommunityAuthorityIsFalse : externalDocumentationCreatesCommunityAuthority ≡ false

canonicalKnowledgeAuthorityBoundary : KnowledgeAuthorityBoundary
canonicalKnowledgeAuthorityBoundary = knowledgeAuthorityBoundary false refl false refl false refl
