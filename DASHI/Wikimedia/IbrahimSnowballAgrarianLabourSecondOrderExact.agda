module DASHI.Wikimedia.IbrahimSnowballAgrarianLabourSecondOrderExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballAgrarianSocietyFoodSecurityPoliticalEconomyBidiExact as Prior
import DASHI.Environment.PeasantAutonomyAgroecologySourceLineageExact as Peasant

------------------------------------------------------------------------
-- IBRAHIM / WIKIDATA SECOND-ORDER WALK: AGRARIAN / LABOUR / FOOD SECURITY
--
-- Followed from the retained first-order QIDs on 2026-09-10.
-- External identities and Wikidata relations are navigation/provenance only.
--
--   social formation             Q1641112
--   community                    Q177634
--   sociology of labour markets  Q112960968
--   labor economics              Q628722
--   labour supply                Q2717283
--   labour demand                Q2355320
--   group of humans              Q16334295
--   worker                       Q327055
--   self-employed person         Q130973804
--   social relation              Q853725
--   security                     Q2526135
--
-- Current candidate seams:
--   agrarian society -> instance social formation; subclass community
--   labour market -> studied by labour sociology / labour economics;
--                    has parts labour supply and labour demand
--   workforce -> group of humans; contains workers and self-employed persons
--   wage labour -> social relation / work
--   food security -> supply/availability/access condition; subclass security
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim second-order agrarian/labour walk"
  "verified external concept identity"
  label
  Identity.wikidataQid
  (Identity.verified qid "Wikidata identity inspected 2026-09-10")

socialFormationQid : Identity.ExternalIdentityDemand
socialFormationQid = mkQid "social formation" "Q1641112"

communityQid : Identity.ExternalIdentityDemand
communityQid = mkQid "community" "Q177634"

labourMarketSociologyQid : Identity.ExternalIdentityDemand
labourMarketSociologyQid = mkQid "sociology of labour markets" "Q112960968"

laborEconomicsQid : Identity.ExternalIdentityDemand
laborEconomicsQid = mkQid "labor economics" "Q628722"

labourSupplyQid : Identity.ExternalIdentityDemand
labourSupplyQid = mkQid "labour supply" "Q2717283"

labourDemandQid : Identity.ExternalIdentityDemand
labourDemandQid = mkQid "labour demand" "Q2355320"

groupOfHumansQid : Identity.ExternalIdentityDemand
groupOfHumansQid = mkQid "group of humans" "Q16334295"

workerQid : Identity.ExternalIdentityDemand
workerQid = mkQid "worker" "Q327055"

selfEmployedQid : Identity.ExternalIdentityDemand
selfEmployedQid = mkQid "self-employed person" "Q130973804"

socialRelationQid : Identity.ExternalIdentityDemand
socialRelationQid = mkQid "social relation" "Q853725"

securityQid : Identity.ExternalIdentityDemand
securityQid = mkQid "security (freedom/resilience from harm)" "Q2526135"

------------------------------------------------------------------------
-- BIDI regression 1: the same workforce count does not recover employment
-- relation. Workforce is a population/group aggregate; wage labour is a social
-- relation and self-employment occupies a different employment relation.
------------------------------------------------------------------------

data WorkforceCase : Set where
  sameWorkforceMostlyWage sameWorkforceMostlySelfEmployed : WorkforceCase

data WorkforceSurface : Set where sameWorkforceAggregate : WorkforceSurface

data LabourRelationReading : Set where wageDependentReading selfEmploymentReading : LabourRelationReading

workforceSurface : WorkforceCase → WorkforceSurface
workforceSurface _ = sameWorkforceAggregate

labourRelationReading : WorkforceCase → LabourRelationReading
labourRelationReading sameWorkforceMostlyWage = wageDependentReading
labourRelationReading sameWorkforceMostlySelfEmployed = selfEmploymentReading

workforceRelationDefect :
  INF.NonFactorabilityWitness workforceSurface labourRelationReading
workforceRelationDefect = INF.nonFactorabilityWitness
  sameWorkforceMostlyWage sameWorkforceMostlySelfEmployed refl (λ ())

workforceCannotFactorLabourRelation :
  INF.FactorsThrough workforceSurface labourRelationReading → ⊥
workforceCannotFactorLabourRelation =
  INF.witnessRulesOutEveryFlatFactorisation workforceRelationDefect

------------------------------------------------------------------------
-- BIDI regression 2: labour-market equilibrium/aggregate cannot recover the
-- producer/worker authority and territorial relation relevant to agrarian LES.
------------------------------------------------------------------------

data LabourMarketCase : Set where
  sameMarketExternalControl sameMarketProducerControlled : LabourMarketCase

data LabourMarketSurface : Set where sameLabourMarketAggregate : LabourMarketSurface

data ProducerAuthorityReading : Set where externallyControlled producerControlled : ProducerAuthorityReading

labourMarketSurface : LabourMarketCase → LabourMarketSurface
labourMarketSurface _ = sameLabourMarketAggregate

producerAuthorityReading : LabourMarketCase → ProducerAuthorityReading
producerAuthorityReading sameMarketExternalControl = externallyControlled
producerAuthorityReading sameMarketProducerControlled = producerControlled

labourMarketAuthorityDefect :
  INF.NonFactorabilityWitness labourMarketSurface producerAuthorityReading
labourMarketAuthorityDefect = INF.nonFactorabilityWitness
  sameMarketExternalControl sameMarketProducerControlled refl (λ ())

labourMarketCannotFactorProducerAuthority :
  INF.FactorsThrough labourMarketSurface producerAuthorityReading → ⊥
labourMarketCannotFactorProducerAuthority =
  INF.witnessRulesOutEveryFlatFactorisation labourMarketAuthorityDefect

------------------------------------------------------------------------
-- BIDI regression 3: supply/availability alone does not recover food security
-- where access differs.  The first-order owner already carries production vs
-- access; here the second-order "security" parent is prevented from erasing it.
------------------------------------------------------------------------

data FoodSecurityCase : Set where
  sameSupplyAccessible sameSupplyInaccessible : FoodSecurityCase

data SupplySurface : Set where sameFoodSupply : SupplySurface

data AccessReading : Set where accessibleFood inaccessibleFood : AccessReading

supplySurface : FoodSecurityCase → SupplySurface
supplySurface _ = sameFoodSupply

accessReading : FoodSecurityCase → AccessReading
accessReading sameSupplyAccessible = accessibleFood
accessReading sameSupplyInaccessible = inaccessibleFood

foodSecurityAccessDefect : INF.NonFactorabilityWitness supplySurface accessReading
foodSecurityAccessDefect = INF.nonFactorabilityWitness
  sameSupplyAccessible sameSupplyInaccessible refl (λ ())

foodSupplyCannotFactorAccess : INF.FactorsThrough supplySurface accessReading → ⊥
foodSupplyCannotFactorAccess =
  INF.witnessRulesOutEveryFlatFactorisation foodSecurityAccessDefect

------------------------------------------------------------------------
-- WrongType and attribution firewalls.
------------------------------------------------------------------------

data WorkforceIsLabourMarket : Set where
data WorkforceIsWageLabour : Set where
data WorkerIsWageLabour : Set where
data AgrarianSocietyIsOneLabourRelation : Set where
data LabourEconomicsIsWorkerVoice : Set where
data FoodSecurityEqualsFoodSovereignty : Set where
data SecurityParentCreatesFoodAccess : Set where

workforceDoesNotBecomeMarket : WorkforceIsLabourMarket → ⊥
workforceDoesNotBecomeMarket ()

workforceDoesNotBecomeWageRelation : WorkforceIsWageLabour → ⊥
workforceDoesNotBecomeWageRelation ()

workerIdentityDoesNotCreateWageRelation : WorkerIsWageLabour → ⊥
workerIdentityDoesNotCreateWageRelation ()

agrarianSocietyDoesNotFixLabourRelation : AgrarianSocietyIsOneLabourRelation → ⊥
agrarianSocietyDoesNotFixLabourRelation ()

labourEconomicsDoesNotCreateWorkerVoice : LabourEconomicsIsWorkerVoice → ⊥
labourEconomicsDoesNotCreateWorkerVoice ()

foodSecurityDoesNotCollapseToFoodSovereignty : FoodSecurityEqualsFoodSovereignty → ⊥
foodSecurityDoesNotCollapseToFoodSovereignty ()

securityParentDoesNotCreateAccessReceipt : SecurityParentCreatesFoodAccess → ⊥
securityParentDoesNotCreateAccessReceipt ()

peasantAttributionBoundary : Peasant.PeasantAutonomyAttributionBoundary
peasantAttributionBoundary = Peasant.canonicalPeasantAutonomyAttributionBoundary

record AgrarianLabourSecondOrderBoundary : Set where
  constructor agrarian-labour-second-order-boundary
  field
    qidsRetainedWhenSafelyResolved : Bool
    externalRelationsCreateSearchObligationsOnly : Bool
    aggregatePopulationAndSocialRelationRemainDistinct : Bool
    labourMarketAndLabourRelationRemainDistinct : Bool
    foodSecurityAndFoodSovereigntyRemainDistinct : Bool
    producerVoiceAndEconomicObserverRemainDistinct : Bool
    attributionTravelsWithMovementClaims : Bool
    twoEyedLESAuthorityMayReopenAggregate : Bool
    presentVocabularyClaimedComplete : Bool
open AgrarianLabourSecondOrderBoundary public

canonicalAgrarianLabourSecondOrderBoundary : AgrarianLabourSecondOrderBoundary
canonicalAgrarianLabourSecondOrderBoundary = agrarian-labour-second-order-boundary
  true true true true true true true true false

priorBoundary : Prior.AgrarianSocietyFoodSecurityPoliticalEconomyBidiBoundary
priorBoundary = Prior.canonicalAgrarianSocietyFoodSecurityPoliticalEconomyBidiBoundary

discoveryBoundary : Discovery.SnowballDiscoveryBoundary
discoveryBoundary = Discovery.canonicalSnowballDiscoveryBoundary
