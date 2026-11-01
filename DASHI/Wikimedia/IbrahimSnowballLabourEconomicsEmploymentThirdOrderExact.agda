module DASHI.Wikimedia.IbrahimSnowballLabourEconomicsEmploymentThirdOrderExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballAgrarianLabourSecondOrderExact as Prior

------------------------------------------------------------------------
-- THIRD-ORDER QID WALK: LABOUR ECONOMICS / EMPLOYMENT / SOCIAL RELATION
--
-- External identities and relations inspected 2026-09-10:
--   economics                    Q8134
--   labor market                 Q305186
--   labor economics              Q628722
--   sociology of labour markets  Q112960968
--   labour supply                Q2717283
--   labour demand                Q2355320
--   worker                       Q327055
--   self-employed person         Q130973804
--   social relation              Q853725
--   employment                   Q656365
--
-- Current Wikidata gives labor economics as a subclass of economics studying
-- the labor market; the labor market has supply and demand and is studied by
-- both labor economics and sociology of labour markets; employment is itself
-- typed as a social relation. These are navigation/type observations only.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim third-order labour/economics walk"
  "verified external concept identity"
  label Identity.wikidataQid
  (Identity.verified qid "Wikidata identity inspected 2026-09-10")

economicsQid : Identity.ExternalIdentityDemand
economicsQid = mkQid "economics" "Q8134"

labourMarketQid : Identity.ExternalIdentityDemand
labourMarketQid = mkQid "labor market" "Q305186"

labourEconomicsQid : Identity.ExternalIdentityDemand
labourEconomicsQid = mkQid "labor economics" "Q628722"

labourMarketSociologyQid : Identity.ExternalIdentityDemand
labourMarketSociologyQid = mkQid "sociology of labour markets" "Q112960968"

labourSupplyQid : Identity.ExternalIdentityDemand
labourSupplyQid = mkQid "labour supply" "Q2717283"

labourDemandQid : Identity.ExternalIdentityDemand
labourDemandQid = mkQid "labour demand" "Q2355320"

workerQid : Identity.ExternalIdentityDemand
workerQid = mkQid "worker" "Q327055"

selfEmployedQid : Identity.ExternalIdentityDemand
selfEmployedQid = mkQid "self-employed person" "Q130973804"

socialRelationQid : Identity.ExternalIdentityDemand
socialRelationQid = mkQid "social relation" "Q853725"

employmentQid : Identity.ExternalIdentityDemand
employmentQid = mkQid "employment" "Q656365"

------------------------------------------------------------------------
-- Regression 1: equal labour-supply totals do not recover worker relation.
------------------------------------------------------------------------

data SupplyCase : Set where
  sameSupplyWageDependent sameSupplySelfEmployed : SupplyCase

data SupplySurface : Set where sameLabourHours : SupplySurface

data WorkerRelation : Set where wageDependentRelation selfEmployedRelation : WorkerRelation

supplySurface : SupplyCase → SupplySurface
supplySurface _ = sameLabourHours

workerRelation : SupplyCase → WorkerRelation
workerRelation sameSupplyWageDependent = wageDependentRelation
workerRelation sameSupplySelfEmployed = selfEmployedRelation

supplyRelationDefect : INF.NonFactorabilityWitness supplySurface workerRelation
supplyRelationDefect = INF.nonFactorabilityWitness
  sameSupplyWageDependent sameSupplySelfEmployed refl (λ ())

labourSupplyCannotFactorWorkerRelation :
  INF.FactorsThrough supplySurface workerRelation → ⊥
labourSupplyCannotFactorWorkerRelation =
  INF.witnessRulesOutEveryFlatFactorisation supplyRelationDefect

------------------------------------------------------------------------
-- Regression 2: equal market-clearing/aggregate surface does not recover
-- bargaining/voice/contestability conditions studied by a social consumer.
------------------------------------------------------------------------

data MarketCase : Set where
  sameMarketLowVoice sameMarketHighVoice : MarketCase

data MarketSurface : Set where sameMarketAggregate : MarketSurface

data VoiceRelation : Set where weakWorkerVoice strongWorkerVoice : VoiceRelation

marketSurface : MarketCase → MarketSurface
marketSurface _ = sameMarketAggregate

voiceRelation : MarketCase → VoiceRelation
voiceRelation sameMarketLowVoice = weakWorkerVoice
voiceRelation sameMarketHighVoice = strongWorkerVoice

marketVoiceDefect : INF.NonFactorabilityWitness marketSurface voiceRelation
marketVoiceDefect = INF.nonFactorabilityWitness
  sameMarketLowVoice sameMarketHighVoice refl (λ ())

labourMarketCannotFactorWorkerVoice :
  INF.FactorsThrough marketSurface voiceRelation → ⊥
labourMarketCannotFactorWorkerVoice =
  INF.witnessRulesOutEveryFlatFactorisation marketVoiceDefect

------------------------------------------------------------------------
-- WrongType boundaries exposed by the QID walk.
------------------------------------------------------------------------

data LaborEconomicsEqualsLaborMarket : Set where
data LaborSupplyEqualsWorker : Set where
data LaborDemandEqualsEmployer : Set where
data EmploymentEqualsWorkforce : Set where
data EmploymentRelationEqualsWorkerIdentity : Set where
data EconomicAggregateCreatesWorkerAuthority : Set where

studyFieldDoesNotBecomeObject : LaborEconomicsEqualsLaborMarket → ⊥
studyFieldDoesNotBecomeObject ()

supplyDoesNotBecomeWorker : LaborSupplyEqualsWorker → ⊥
supplyDoesNotBecomeWorker ()

demandDoesNotBecomeEmployer : LaborDemandEqualsEmployer → ⊥
demandDoesNotBecomeEmployer ()

employmentDoesNotBecomeWorkforce : EmploymentEqualsWorkforce → ⊥
employmentDoesNotBecomeWorkforce ()

relationDoesNotBecomePersonIdentity : EmploymentRelationEqualsWorkerIdentity → ⊥
relationDoesNotBecomePersonIdentity ()

economicAggregateDoesNotCreateWorkerAuthority : EconomicAggregateCreatesWorkerAuthority → ⊥
economicAggregateDoesNotCreateWorkerAuthority ()

record LabourEconomicsEmploymentThirdOrderBoundary : Set where
  constructor labour-economics-employment-third-order-boundary
  field
    qidsRetainedWhenSafelyResolved : Bool
    studyFieldObjectAndRelationRemainDistinct : Bool
    supplyDemandRemainMarketCoordinates : Bool
    workerAndSelfEmploymentRolesRemainDistinct : Bool
    employmentRetainedAsSocialRelation : Bool
    economicAggregateDoesNotExhaustSocialRelation : Bool
    workerVoiceMayRequireRicherConsumerLens : Bool
    attributionTravelsWithNewGraphAtoms : Bool
    presentVocabularyClaimedComplete : Bool
open LabourEconomicsEmploymentThirdOrderBoundary public

canonicalLabourEconomicsEmploymentThirdOrderBoundary :
  LabourEconomicsEmploymentThirdOrderBoundary
canonicalLabourEconomicsEmploymentThirdOrderBoundary =
  labour-economics-employment-third-order-boundary
    true true true true true true true true false

priorBoundary : Prior.AgrarianLabourSecondOrderBoundary
priorBoundary = Prior.canonicalAgrarianLabourSecondOrderBoundary
