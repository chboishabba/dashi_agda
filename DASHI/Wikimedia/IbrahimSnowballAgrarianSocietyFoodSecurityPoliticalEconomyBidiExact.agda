module DASHI.Wikimedia.IbrahimSnowballAgrarianSocietyFoodSecurityPoliticalEconomyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballAnthropologyAgricultureLESExact as Agriculture
import DASHI.Environment.PeasantAutonomyAgroecologySourceLineageExact as Peasant

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL BIDI CONTINUATION:
--
--   agriculture / agroecology / LES
--       <-> agrarian society / rural community
--       <-> food system / food security
--       <-> labour / land / market relations
--       <-> economics / health / access / political economy
--
-- Parent graph nodes are navigation candidates only. Concrete access,
-- distribution, labour, territory and source-role counterexamples constrain
-- the broader nodes in return.
--
-- External identities checked 2026-09-10:
--   agrarian society Q396108
--   food security    Q1229911
--   labour market    Q305186
--   workforce        Q13440398
--   wage labour      Q949973
--
-- Exact generic land-tenure and food-system QIDs remain unresolved in this
-- owner rather than promoting nearby category or sector items.
------------------------------------------------------------------------

agrarianSocietyQid : Identity.ExternalIdentityDemand
agrarianSocietyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim agrarian/food-system BIDI" "external concept identity"
  "agrarian society" Identity.wikidataQid
  (Identity.verified "Q396108" "Wikidata identity checked 2026-09-10")

foodSecurityQid : Identity.ExternalIdentityDemand
foodSecurityQid = Identity.mkOptionalIdentityDemand
  "Ibrahim agrarian/food-system BIDI" "external concept identity"
  "food security" Identity.wikidataQid
  (Identity.verified "Q1229911" "Wikidata identity checked 2026-09-10")

labourMarketQid : Identity.ExternalIdentityDemand
labourMarketQid = Identity.mkOptionalIdentityDemand
  "Ibrahim agrarian/food-system BIDI" "external concept identity"
  "labour market" Identity.wikidataQid
  (Identity.verified "Q305186" "Wikidata identity checked 2026-09-10")

workforceQid : Identity.ExternalIdentityDemand
workforceQid = Identity.mkOptionalIdentityDemand
  "Ibrahim agrarian/food-system BIDI" "external concept identity"
  "workforce" Identity.wikidataQid
  (Identity.verified "Q13440398" "Wikidata identity checked 2026-09-10")

wageLabourQid : Identity.ExternalIdentityDemand
wageLabourQid = Identity.mkOptionalIdentityDemand
  "Ibrahim agrarian/food-system BIDI" "external concept identity"
  "wage labour" Identity.wikidataQid
  (Identity.verified "Q949973" "Wikidata identity checked 2026-09-10")

landTenureQid : Identity.ExternalIdentityDemand
landTenureQid = Identity.mkOptionalIdentityDemand
  "Ibrahim agrarian/food-system BIDI" "external concept identity"
  "land tenure" Identity.wikidataQid
  (Identity.unresolved "exact concept identity not safely resolved; nearby category/property items are not promoted")

foodSystemQid : Identity.ExternalIdentityDemand
foodSystemQid = Identity.mkOptionalIdentityDemand
  "Ibrahim agrarian/food-system BIDI" "external concept identity"
  "food system / agrifood system" Identity.wikidataQid
  (Identity.unresolved "exact broad parent identity not safely fixed in this tranche")

------------------------------------------------------------------------
-- Exact regression 1: equal food-production/availability surfaces need not
-- recover access/distribution security. Production cannot answer every food-
-- security consumer.
------------------------------------------------------------------------

data FoodAccessCase : Set where
  sameProductionRestrictedAccess sameProductionBroadAccess : FoodAccessCase

data ProductionSurface : Set where sameFoodProduction : ProductionSurface
data FoodAccessReading : Set where accessRestricted accessBroad : FoodAccessReading

productionSurface : FoodAccessCase → ProductionSurface
productionSurface _ = sameFoodProduction

foodAccessReading : FoodAccessCase → FoodAccessReading
foodAccessReading sameProductionRestrictedAccess = accessRestricted
foodAccessReading sameProductionBroadAccess = accessBroad

productionAccessDefect : INF.NonFactorabilityWitness productionSurface foodAccessReading
productionAccessDefect = INF.nonFactorabilityWitness
  sameProductionRestrictedAccess sameProductionBroadAccess refl (λ ())

productionCannotFactorFoodAccess :
  INF.FactorsThrough productionSurface foodAccessReading → ⊥
productionCannotFactorFoodAccess =
  INF.witnessRulesOutEveryFlatFactorisation productionAccessDefect

------------------------------------------------------------------------
-- Exact regression 2: a shared agrarian-society label cannot recover land,
-- labour or authority relations.
------------------------------------------------------------------------

data AgrarianPoliticalCase : Set where
  sameAgrarianLabelConcentratedControl sameAgrarianLabelDistributedControl : AgrarianPoliticalCase

data AgrarianSocietySurface : Set where sameAgrarianSociety : AgrarianSocietySurface
data AgrarianControlReading : Set where concentratedControl distributedCommunityControl : AgrarianControlReading

agrarianSocietySurface : AgrarianPoliticalCase → AgrarianSocietySurface
agrarianSocietySurface _ = sameAgrarianSociety

agrarianControlReading : AgrarianPoliticalCase → AgrarianControlReading
agrarianControlReading sameAgrarianLabelConcentratedControl = concentratedControl
agrarianControlReading sameAgrarianLabelDistributedControl = distributedCommunityControl

agrarianControlDefect : INF.NonFactorabilityWitness agrarianSocietySurface agrarianControlReading
agrarianControlDefect = INF.nonFactorabilityWitness
  sameAgrarianLabelConcentratedControl sameAgrarianLabelDistributedControl refl (λ ())

agrarianLabelCannotFactorControlRelation :
  INF.FactorsThrough agrarianSocietySurface agrarianControlReading → ⊥
agrarianLabelCannotFactorControlRelation =
  INF.witnessRulesOutEveryFlatFactorisation agrarianControlDefect

------------------------------------------------------------------------
-- Exact regression 3: a labour-market summary cannot recover worker role or
-- voice merely from participation/employment counts.
------------------------------------------------------------------------

data LabourCase : Set where
  sameMarketWageLabourLowVoice sameMarketAutonomousProducerHighVoice : LabourCase

data LabourMarketSurface : Set where sameLabourMarket : LabourMarketSurface
data LabourRelationReading : Set where wageDependentLowVoice autonomousProducerHighVoice : LabourRelationReading

labourMarketSurface : LabourCase → LabourMarketSurface
labourMarketSurface _ = sameLabourMarket

labourRelationReading : LabourCase → LabourRelationReading
labourRelationReading sameMarketWageLabourLowVoice = wageDependentLowVoice
labourRelationReading sameMarketAutonomousProducerHighVoice = autonomousProducerHighVoice

labourRelationDefect : INF.NonFactorabilityWitness labourMarketSurface labourRelationReading
labourRelationDefect = INF.nonFactorabilityWitness
  sameMarketWageLabourLowVoice sameMarketAutonomousProducerHighVoice refl (λ ())

labourMarketCannotFactorLabourRelation :
  INF.FactorsThrough labourMarketSurface labourRelationReading → ⊥
labourMarketCannotFactorLabourRelation =
  INF.witnessRulesOutEveryFlatFactorisation labourRelationDefect

------------------------------------------------------------------------
-- Attribution / Two-Eyed / source-role constraints reused from agrarian lane.
------------------------------------------------------------------------

foodSovereigntyDoesNotProveFoodSecurity :
  Peasant.FoodSovereigntyMeansFoodSecurityOutcomePermission → ⊥
foodSovereigntyDoesNotProveFoodSecurity =
  Peasant.foodSovereigntyDoesNotByItselfProveFoodSecurityOutcome

peasantAttributionBoundary : Peasant.PeasantAutonomyAttributionBoundary
peasantAttributionBoundary = Peasant.canonicalPeasantAutonomyAttributionBoundary

priorAgricultureBoundary : Agriculture.AnthropologyAgricultureLESSnowballBoundary
priorAgricultureBoundary = Agriculture.canonicalAnthropologyAgricultureLESSnowballBoundary

data FoodSecurityEqualsFoodSovereignty : Set where
data FoodProductionCreatesFoodAccess : Set where
data LabourMarketEqualsWorkforce : Set where
data WorkforceEqualsWageLabour : Set where
data LandUseCreatesLandAuthority : Set where
data EconomicAggregateErasesProducerVoice : Set where

foodSecurityDoesNotEqualFoodSovereignty : FoodSecurityEqualsFoodSovereignty → ⊥
foodSecurityDoesNotEqualFoodSovereignty ()

foodProductionDoesNotCreateAccess : FoodProductionCreatesFoodAccess → ⊥
foodProductionDoesNotCreateAccess ()

labourMarketDoesNotEqualWorkforce : LabourMarketEqualsWorkforce → ⊥
labourMarketDoesNotEqualWorkforce ()

workforceDoesNotEqualWageLabour : WorkforceEqualsWageLabour → ⊥
workforceDoesNotEqualWageLabour ()

landUseDoesNotCreateLandAuthority : LandUseCreatesLandAuthority → ⊥
landUseDoesNotCreateLandAuthority ()

economicAggregateDoesNotEraseProducerVoice : EconomicAggregateErasesProducerVoice → ⊥
economicAggregateDoesNotEraseProducerVoice ()

record AgrarianSocietyFoodSecurityPoliticalEconomyBidiBoundary : Set where
  constructor agrarian-society-food-security-political-economy-bidi-boundary
  field
    exactQidsAttachedWhenSafelyResolvable : Bool
    unresolvedLandTenureIdentityRetained : Bool
    productionDoesNotDetermineAccess : Bool
    foodSecurityAndFoodSovereigntyRemainDistinct : Bool
    agrarianLabelDoesNotDetermineControlRelation : Bool
    labourMarketWorkforceAndWageLabourRemainDistinct : Bool
    producerCommunityVoiceRetainedWhenRelevant : Bool
    territoryAndAuthorityRemainSourceBound : Bool
    scientificAgronomyDoesNotExhaustPoliticalEconomy : Bool
    twoEyedMaterialAndSituatedReadingsRetained : Bool
    currentAxisVocabularyClaimedComplete : Bool
open AgrarianSocietyFoodSecurityPoliticalEconomyBidiBoundary public

canonicalAgrarianSocietyFoodSecurityPoliticalEconomyBidiBoundary :
  AgrarianSocietyFoodSecurityPoliticalEconomyBidiBoundary
canonicalAgrarianSocietyFoodSecurityPoliticalEconomyBidiBoundary =
  agrarian-society-food-security-political-economy-bidi-boundary
    true true true true true true true true true true false
