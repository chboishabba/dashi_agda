module DASHI.Core.CategoryAuthorityAuditExact where

------------------------------------------------------------------------
-- CATEGORY AUTHORITY / GENESIS AUDIT
--
-- Internal technical adequacy of a category does not establish historical,
-- political or epistemic neutrality of the category's genesis.  This is a
-- formalisation-governance owner, not a claim that any particular scientific
-- category is invalid.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record CategoryAuthorityAudit : Set₁ where
  constructor categoryAuthorityAudit
  field
    Category : Set
    TechnicalAdequacy : Category → Set
    GenesisAccountedFor : Category → Set
    PoliticalNeutrality : Category → Set
    SemanticallyExhaustive : Category → Set

open CategoryAuthorityAudit public

record TechnicallyAdequateCategory (audit : CategoryAuthorityAudit) : Set₁ where
  constructor technicallyAdequateCategory
  field
    category : Category audit
    technicalAdequacy : TechnicalAdequacy audit category

open TechnicallyAdequateCategory public

record CategoryGenesisResidual (audit : CategoryAuthorityAudit) : Set₁ where
  constructor categoryGenesisResidual
  field
    category : Category audit
    genesisNotAccountedFor : GenesisAccountedFor audit category → ⊥

open CategoryGenesisResidual public

record CategoryAuthorityBoundary : Set where
  constructor categoryAuthorityBoundary
  field
    technicalAdequacyImpliesGenesisAccountedFor : Bool
    technicalAdequacyImpliesGenesisAccountedForIsFalse :
      technicalAdequacyImpliesGenesisAccountedFor ≡ false
    technicalAdequacyImpliesPoliticalNeutrality : Bool
    technicalAdequacyImpliesPoliticalNeutralityIsFalse :
      technicalAdequacyImpliesPoliticalNeutrality ≡ false
    completeDataImpliesSemanticExhaustiveness : Bool
    completeDataImpliesSemanticExhaustivenessIsFalse :
      completeDataImpliesSemanticExhaustiveness ≡ false
    genesisCritiqueImpliesTechnicalInvalidity : Bool
    genesisCritiqueImpliesTechnicalInvalidityIsFalse :
      genesisCritiqueImpliesTechnicalInvalidity ≡ false

canonicalCategoryAuthorityBoundary : CategoryAuthorityBoundary
canonicalCategoryAuthorityBoundary =
  categoryAuthorityBoundary false refl false refl false refl false refl
