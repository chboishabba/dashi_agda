module DASHI.Wikimedia.IbrahimDisposableVapeWasteFireParetoExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimDisposableVapeBatteryWasteFireExternalityExact as Fire

------------------------------------------------------------------------
-- PURPOSE
--
-- Two different consumers must not be collapsed:
--   (1) reduce the probability that embedded vape batteries enter mixed waste
--       and trigger collection / processing fires;
--   (2) improve attribution so we can estimate the vape-specific share of
--       battery-related waste fires.
--
-- Cross-consumer ordering is roadmap preference, not scientific dominance.
------------------------------------------------------------------------

data WasteFireConsumer : Set where
  mixedWasteFirePrevention : WasteFireConsumer
  vapeSpecificFireAttribution : WasteFireConsumer

data PreventionCandidate : Set where
  informationOnly : PreventionCandidate
  councilHazardousWasteDropOff : PreventionCandidate
  pointOfSaleTakeBack : PreventionCandidate
  producerResponsibilityEmbeddedBatteryCollection : PreventionCandidate
  designForRecoverableBattery : PreventionCandidate

data AttributionCandidate : Set where
  genericBatteryFireCoding : AttributionCandidate
  embeddedDeviceCategoryCoding : AttributionCandidate
  vapeSpecificIncidentCoding : AttributionCandidate
  incidentPlusRecoveredObjectForensics : AttributionCandidate
  incidentPlusWasteStreamDenominator : AttributionCandidate

------------------------------------------------------------------------
-- SOURCE-BOUNDED CURRENT ARCHITECTURES
------------------------------------------------------------------------

record ArchitectureReceipt : Set where
  constructor architecture-receipt
  field
    name : String
    jurisdiction : String
    carrier : String
    supportedClaim : String
    excludedPromotion : String
open ArchitectureReceipt public

bcycleEmbeddedGap : ArchitectureReceipt
bcycleEmbeddedGap = architecture-receipt
  "B-cycle acceptance boundary"
  "Australia"
  "official battery-stewardship scheme"
  "B-cycle accepts small loose/easily removable batteries but does not accept vape batteries or batteries embedded in devices"
  "existence of a national battery scheme does not imply an accessible disposal path for whole disposable vapes"

brisbaneVapeDropOff : ArchitectureReceipt
brisbaneVapeDropOff = architecture-receipt
  "Brisbane resource-recovery-centre vape acceptance"
  "Brisbane, Queensland"
  "local-government hazardous-waste / resource-recovery system"
  "Brisbane resource recovery centres accept household quantities of vapes/e-cigarettes as battery-containing hazardous items"
  "local acceptance does not establish national coverage, participation, effect size, or fire reduction"

nswEmbeddedTrial : ArchitectureReceipt
nswEmbeddedTrial = architecture-receipt
  "NSW embedded-battery collection trial"
  "New South Wales"
  "community recycling / Household Chemical CleanOut"
  "NSW EPA trial accepts vapes as embedded-battery items at participating services through September 2026"
  "trial availability does not imply universal NSW coverage or measured causal reduction in fires"

nswProducerResponsibility : ArchitectureReceipt
nswProducerResponsibility = architecture-receipt
  "NSW battery producer-responsibility reform"
  "New South Wales"
  "mandatory battery regulation announced April 2026"
  "brand owners are required to take responsibility for end-of-life battery collection, processing and recycling under NSW reform"
  "a statutory architecture does not itself pay realised diversion, compliance, or vape-specific fire reduction"

------------------------------------------------------------------------
-- PREVENTION PARETO PROFILE
--
-- All axes are local design coordinates, not measured dollars, effect sizes,
-- legal feasibility, or certified risk reduction.
------------------------------------------------------------------------

record PreventionProfile : Set where
  constructor prevention-profile
  field
    candidate : PreventionCandidate
    embeddedDeviceCompatibility : Nat
    userConvenience : Nat
    sourceInterception : Nat
    producerInternalisation : Nat
    implementationBurden : Nat
    dependenceOnUserKnowledge : Nat
    measuredFireReductionPaid : Bool
open PreventionProfile public

informationProfile : PreventionProfile
informationProfile = prevention-profile
  informationOnly 1 2 1 0 1 5 false

dropOffProfile : PreventionProfile
dropOffProfile = prevention-profile
  councilHazardousWasteDropOff 5 3 3 1 2 4 false

retailerTakeBackProfile : PreventionProfile
retailerTakeBackProfile = prevention-profile
  pointOfSaleTakeBack 5 5 4 3 3 2 false

producerResponsibilityProfile : PreventionProfile
producerResponsibilityProfile = prevention-profile
  producerResponsibilityEmbeddedBatteryCollection 5 4 5 5 4 2 false

recoverableDesignProfile : PreventionProfile
recoverableDesignProfile = prevention-profile
  designForRecoverableBattery 5 4 5 5 5 2 false

------------------------------------------------------------------------
-- ATTRIBUTION / DENOMINATOR PARETO PROFILE
------------------------------------------------------------------------

record AttributionProfile : Set where
  constructor attribution-profile
  field
    candidate : AttributionCandidate
    vapeSpecificity : Nat
    causalConfidence : Nat
    denominatorQuality : Nat
    dataBurden : Nat
    forensicBurden : Nat
    nationalRatePaid : Bool
open AttributionProfile public

genericCodingProfile : AttributionProfile
genericCodingProfile = attribution-profile
  genericBatteryFireCoding 1 2 0 1 0 false

embeddedCategoryProfile : AttributionProfile
embeddedCategoryProfile = attribution-profile
  embeddedDeviceCategoryCoding 2 2 0 2 0 false

vapeCodingProfile : AttributionProfile
vapeCodingProfile = attribution-profile
  vapeSpecificIncidentCoding 4 2 0 3 0 false

forensicProfile : AttributionProfile
forensicProfile = attribution-profile
  incidentPlusRecoveredObjectForensics 5 5 0 4 5 false

denominatorProfile : AttributionProfile
denominatorProfile = attribution-profile
  incidentPlusWasteStreamDenominator 5 4 5 5 3 false

------------------------------------------------------------------------
-- COLLISIONS / WRONG-TYPE GUARDS
------------------------------------------------------------------------

record ParetoCollision : Set where
  constructor pareto-collision
  field
    consumer : WasteFireConsumer
    coarseArchitecture : String
    worldA : String
    worldB : String
    sameCoarseObservation : Bool
    differentConsumerAnswer : Bool
    missingCoordinate : String
open ParetoCollision public

batterySchemeCollision : ParetoCollision
batterySchemeCollision = pareto-collision
  mixedWasteFirePrevention
  "a national battery-recycling scheme exists"
  "scheme accepts the whole embedded-battery vape"
  "scheme accepts only loose/easily removable batteries and excludes vapes"
  true true
  "embedded-device acceptance / practical disposal path"

fireCodingCollision : ParetoCollision
fireCodingCollision = pareto-collision
  vapeSpecificFireAttribution
  "incident coded battery-related"
  "battery source is a disposable vape"
  "battery source is another device class"
  true true
  "vape-specific object attribution"

denominatorCollision : ParetoCollision
denominatorCollision = pareto-collision
  vapeSpecificFireAttribution
  "count of vape-coded fires"
  "few vapes discarded into mixed waste"
  "many vapes discarded into mixed waste"
  true true
  "discarded-vape / waste-stream denominator"

------------------------------------------------------------------------
-- CONSUMER INDEXING
------------------------------------------------------------------------

data FirePreventionConsumerIndexed : Set where
  prevention-indexed : FirePreventionConsumerIndexed

data VapeFireAttributionConsumerIndexed : Set where
  attribution-indexed : VapeFireAttributionConsumerIndexed

data EmbeddedBatterySchemeGapRetained : Set where
  embedded-gap-retained : EmbeddedBatterySchemeGapRetained

------------------------------------------------------------------------
-- ROADMAP PREFERENCE
------------------------------------------------------------------------

record WasteFireRoadmapPreference : Set where
  constructor waste-fire-roadmap-preference
  field
    preventionFirst : PreventionCandidate
    attributionFirst : AttributionCandidate
    preventionReason : String
    attributionReason : String
    crossConsumerScientificDominanceClaimed : Bool
    measuredEffectClaimed : Bool
    authorityClaimed : Bool
open WasteFireRoadmapPreference public

canonicalWasteFireRoadmapPreference : WasteFireRoadmapPreference
canonicalWasteFireRoadmapPreference = waste-fire-roadmap-preference
  pointOfSaleTakeBack
  vapeSpecificIncidentCoding
  "local synthetic preference: intercept a whole embedded-battery product at a familiar hand-back point, avoiding the B-cycle embedded-device acceptance gap; not an empirical claim that retailer take-back is globally optimal"
  "first improve incident coding before paying expensive forensic/denominator systems; coded vape incidents are needed to measure the specific problem"
  false false false

------------------------------------------------------------------------
-- HARD FIREWALLS
------------------------------------------------------------------------

data ParetoFrontCreatesAuthority : Set where
data GlobalOptimalityFromDeclaredLanguage : Set where
data SyntheticProfileCreatesMeasuredEffect : Set where
data BatterySchemeCreatesVapeAcceptance : Set where
data CrossConsumerProfileCreatesScientificDominance : Set where
data LocalCollectionArchitectureCreatesNationalCoverage : Set where

paretoNotAuthority : ParetoFrontCreatesAuthority → ⊥
paretoNotAuthority ()

globalNotPaid : GlobalOptimalityFromDeclaredLanguage → ⊥
globalNotPaid ()

syntheticNotEffect : SyntheticProfileCreatesMeasuredEffect → ⊥
syntheticNotEffect ()

batterySchemeNotVapeAcceptance : BatterySchemeCreatesVapeAcceptance → ⊥
batterySchemeNotVapeAcceptance ()

crossConsumerNotDominance : CrossConsumerProfileCreatesScientificDominance → ⊥
crossConsumerNotDominance ()

localNotNational : LocalCollectionArchitectureCreatesNationalCoverage → ⊥
localNotNational ()

record WasteFireParetoBoundary : Set where
  constructor waste-fire-pareto-boundary
  field
    preventionAndAttributionSeparateConsumers : Bool
    embeddedDeviceAcceptanceCoordinateRequired : Bool
    measuredEffectSizePaid : Bool
    nationalVapeFireRatePaid : Bool
    boundedCandidateLanguageOnly : Bool
    paretoCreatesAuthority : Bool
open WasteFireParetoBoundary public

canonicalWasteFireParetoBoundary : WasteFireParetoBoundary
canonicalWasteFireParetoBoundary = waste-fire-pareto-boundary
  true true false false true false

externalityEvidenceRetained : Bool
externalityEvidenceRetained = Fire.generalBatteryRiskPaid Fire.canonicalWasteFireBoundary
