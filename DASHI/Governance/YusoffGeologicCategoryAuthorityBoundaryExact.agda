module DASHI.Governance.YusoffGeologicCategoryAuthorityBoundaryExact where

open import DASHI.Core.Prelude
import DASHI.Core.CategoryAuthorityAuditExact as Category
import DASHI.Governance.FeministClimateJusticeSourceRegistryExact as Sources

------------------------------------------------------------------------
-- YUSOFF: TECHNICAL CATEGORY USE != HISTORICAL / POLITICAL NEUTRALITY
--
-- Kathryn Yusoff, A Billion Black Anthropocenes or None,
-- University of Minnesota Press, 2018.
-- Paperback ISBN 9781517907532; eBook ISBN 9781452961057.
--
-- The source motivates an audit of geology / Anthropocene category genesis in
-- relation to extraction, colonialism, slavery and race.  This module does NOT
-- claim that geology is scientifically invalid, that planetary-boundary science
-- is definitionally racist, or that a category-genesis critique refutes every
-- technical theorem expressed with the category.
------------------------------------------------------------------------

data GeologicCategory : Set where anthropoceneCategory : GeologicCategory

data TechnicalAdequacy : GeologicCategory → Set where
  technicallyUsableAnthropocene : TechnicalAdequacy anthropoceneCategory

data GenesisAccountedFor : GeologicCategory → Set where

data PoliticalNeutrality : GeologicCategory → Set where

data SemanticallyExhaustive : GeologicCategory → Set where

yusoffAudit : Category.CategoryAuthorityAudit
yusoffAudit =
  Category.categoryAuthorityAudit
    GeologicCategory
    TechnicalAdequacy
    GenesisAccountedFor
    PoliticalNeutrality
    SemanticallyExhaustive

technicalUseReceipt : Category.TechnicallyAdequateCategory yusoffAudit
technicalUseReceipt =
  Category.technicallyAdequateCategory anthropoceneCategory technicallyUsableAnthropocene

categoryGenesisResidual : Category.CategoryGenesisResidual yusoffAudit
categoryGenesisResidual =
  Category.categoryGenesisResidual anthropoceneCategory (λ ())

technicalUseDoesNotSupplyGenesisAccounting :
  GenesisAccountedFor anthropoceneCategory → ⊥
technicalUseDoesNotSupplyGenesisAccounting ()

technicalUseDoesNotSupplyPoliticalNeutrality :
  PoliticalNeutrality anthropoceneCategory → ⊥
technicalUseDoesNotSupplyPoliticalNeutrality ()

technicalUseDoesNotSupplySemanticExhaustiveness :
  SemanticallyExhaustive anthropoceneCategory → ⊥
technicalUseDoesNotSupplySemanticExhaustiveness ()

source : Sources.SourceReference
source = Sources.yusoff2018

record YusoffCategoryAuthorityBoundary : Set where
  constructor yusoffCategoryAuthorityBoundary
  field
    technicalUseImpliesHistoricallyNeutralGenesis : Bool
    technicalUseImpliesHistoricallyNeutralGenesisIsFalse :
      technicalUseImpliesHistoricallyNeutralGenesis ≡ false
    completeDataWithinCategoryImpliesCategoryNeutrality : Bool
    completeDataWithinCategoryImpliesCategoryNeutralityIsFalse :
      completeDataWithinCategoryImpliesCategoryNeutrality ≡ false
    categoryGenesisCritiqueImpliesScientificInvalidity : Bool
    categoryGenesisCritiqueImpliesScientificInvalidityIsFalse :
      categoryGenesisCritiqueImpliesScientificInvalidity ≡ false
    yusoffBookIsPlanetaryBoundaryRefutation : Bool
    yusoffBookIsPlanetaryBoundaryRefutationIsFalse :
      yusoffBookIsPlanetaryBoundaryRefutation ≡ false

canonicalYusoffCategoryAuthorityBoundary : YusoffCategoryAuthorityBoundary
canonicalYusoffCategoryAuthorityBoundary =
  yusoffCategoryAuthorityBoundary false refl false refl false refl false refl
