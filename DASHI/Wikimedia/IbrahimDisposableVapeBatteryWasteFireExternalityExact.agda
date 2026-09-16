module DASHI.Wikimedia.IbrahimDisposableVapeBatteryWasteFireExternalityExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- BATTERY / VAPE WASTE-FIRE EXTERNALITY
--
-- Keep fire-service incidents, waste-industry estimates, confirmed causes,
-- suspected causes and vape-specific attributions as distinct evidence types.
------------------------------------------------------------------------

data AttributionGrade : Set where
  confirmedBatteryCause
  suspectedBatteryCause
  possibleBatteryCause
  industryBatteryEstimate
  industryVapeSpecificEstimate
  vapeSpecificRecordedIncident : AttributionGrade

record FireIncidenceReceipt : Set where
  constructor fire-incidence-receipt
  field
    geography : String
    period : String
    countOrRate : String
    carrier : String
    attribution : AttributionGrade
    source : String
    sourceKind : String
    supportedClaim : String
    excludedPromotion : String
open FireIncidenceReceipt public

nsw2025BatteryIncidents : FireIncidenceReceipt
nsw2025BatteryIncidents = fire-incidence-receipt
  "New South Wales"
  "2025"
  "332 lithium-ion-battery-related incidents recorded by Fire and Rescue NSW"
  "community plus waste-system incidents"
  suspectedBatteryCause
  "NSW Government / FRNSW, 7 April 2026"
  "official government/fire-service statistic"
  "battery-related fire burden is substantial and increasing"
  "does not mean 332 waste-bin fires or 332 vape-caused fires"

nsw2026WasteConfirmedSuspected : FireIncidenceReceipt
nsw2026WasteConfirmedSuspected = fire-incidence-receipt
  "New South Wales"
  "2026 year-to-7-April reporting window"
  "at least 12 battery fires in garbage trucks/waste facilities/tips plus 103 further waste-industry fires suspected to involve batteries"
  "waste system"
  suspectedBatteryCause
  "NSW Government / EPA"
  "official government statistic"
  "confirmed/recorded battery waste incidents and larger suspected-battery cohort must remain separate"
  "does not create a national annual rate or vape-specific attribution"

nsw2025GarbageTruck : FireIncidenceReceipt
nsw2025GarbageTruck = fire-incidence-receipt
  "New South Wales"
  "2025"
  "62 garbage-truck fires"
  "garbage collection vehicles"
  possibleBatteryCause
  "Fire and Rescue NSW, 12 August 2026"
  "official fire-service count"
  "garbage-truck fire burden is independently observable; FRNSW says most are believed to have been caused by lithium-ion batteries in household rubbish"
  "not every one of the 62 is individually confirmed battery-caused"

brisbaneHotLoads : FireIncidenceReceipt
brisbaneHotLoads = fire-incidence-receipt
  "Brisbane"
  "five years to August 2024"
  "43 hot loads; 140 rubbish fires since 2019"
  "garbage trucks and resource-recovery centres"
  suspectedBatteryCause
  "Brisbane City Council figures reported by ABC, 20 August 2024"
  "local-government figures reported by public broadcaster"
  "battery/flammable contamination causes recurring truck and facility incidents in Brisbane"
  "140 rubbish fires are not all battery-caused and 43 hot loads are not all vape-caused"

queenslandVapeIndustryEstimate : FireIncidenceReceipt
queenslandVapeIndustryEstimate = fire-incidence-receipt
  "Queensland"
  "reported December 2023"
  "at least five fires per day in recycling plants attributed by industry experts to disposable vapes/lithium-ion batteries"
  "recycling facilities"
  industryVapeSpecificEstimate
  "National Waste and Recycling Industry Council CEO quoted by ABC"
  "industry estimate"
  "vapes were reported as a material contributor to frequent recycling-facility fires"
  "not an official fire-service incident register; do not multiply to a certified national count"

ukBatteryWaste2023 : FireIncidenceReceipt
ukBatteryWaste2023 = fire-incidence-receipt
  "United Kingdom"
  "2023 / last-12-month survey published May 2024"
  "over 1,200 battery fires in bin lorries and waste sites, up 71% from about 700 in 2022"
  "bin lorries and waste sites"
  industryBatteryEstimate
  "Material Focus local-authority research / National Fire Chiefs Council"
  "national local-authority survey promoted by NFCC"
  "battery fires in waste streams are frequent and rising"
  "survey estimate is not an incident-by-incident fire-service census and is not vape-specific"

northLondonVape2025 : FireIncidenceReceipt
northLondonVape2025 = fire-incidence-receipt
  "North London Waste Authority"
  "2025"
  "3 incidents with suspected cause recorded as vape-related"
  "NLWA waste facilities"
  vapeSpecificRecordedIncident
  "NLWA FOI response 20 May 2026"
  "authority-held incident record"
  "vape-specific waste fires can be separately recorded where cause coding exists"
  "absence of earlier vape-coded data does not imply zero earlier vape fires"

usEPA2013to2020 : FireIncidenceReceipt
usEPA2013to2020 = fire-incidence-receipt
  "United States"
  "2013-2020"
  "245 fires at 64 waste-management facilities in 28 states caused by or likely caused by lithium metal/lithium-ion batteries"
  "MRFs, garbage trucks, landfills, recyclers and transfer stations"
  suspectedBatteryCause
  "US EPA Analysis of Lithium-ion Battery Fires in Waste Management and Recycling"
  "federal retrospective incident study"
  "lithium batteries are a documented waste-system ignition source with injuries, service disruption and monetary loss"
  "historical US sample does not provide a current national annual rate or vape-specific fraction"

------------------------------------------------------------------------
-- ATTRIBUTION / DENOMINATOR FIREWALLS
------------------------------------------------------------------------

data BatteryRelatedCreatesVapeCause : Set where
data SuspectedCreatesConfirmed : Set where
data LocalRateCreatesNationalRate : Set where
data UncodedVapeCauseCreatesZeroVapeFires : Set where
data WasteFireCountCreatesCommunityBatteryCount : Set where

batteryNotVape : BatteryRelatedCreatesVapeCause → ⊥
batteryNotVape ()

suspectedNotConfirmed : SuspectedCreatesConfirmed → ⊥
suspectedNotConfirmed ()

localNotNational : LocalRateCreatesNationalRate → ⊥
localNotNational ()

uncodedNotZero : UncodedVapeCauseCreatesZeroVapeFires → ⊥
uncodedNotZero ()

wasteNotCommunity : WasteFireCountCreatesCommunityBatteryCount → ⊥
wasteNotCommunity ()

------------------------------------------------------------------------
-- EXTERNALITY CHAIN
------------------------------------------------------------------------

record WasteFireExternalityChain : Set where
  constructor waste-fire-externality-chain
  field
    embeddedBattery : String
    incorrectDisposal : String
    mechanicalTrigger : String
    failureMode : String
    exposureCarrier : String
    downstreamEffects : String
open WasteFireExternalityChain public

canonicalWasteFireExternality : WasteFireExternalityChain
canonicalWasteFireExternality = waste-fire-externality-chain
  "lithium-ion cell embedded in vape/electrical product"
  "general rubbish or mixed recycling rather than dedicated battery/e-waste stream"
  "compaction, crushing, puncture, shorting or other damage during collection/sorting"
  "thermal runaway / ignition"
  "household bin -> collection truck -> transfer/recycling facility -> landfill/waste site"
  "worker/public risk, emergency response, service interruption, equipment/property loss, smoke/air-pollution externality"

record WasteFireBoundary : Set where
  constructor waste-fire-boundary
  field
    generalBatteryRiskPaid : Bool
    officialAustralianWasteCountsPaid : Bool
    vapeSpecificRecordedIncidentsPaid : Bool
    vapeSpecificIndustryRatePaid : Bool
    nationalAustraliaVapeFireRatePaid : Bool
    exactBatteryTypeAttributionUsuallyPaid : Bool
open WasteFireBoundary public

canonicalWasteFireBoundary : WasteFireBoundary
canonicalWasteFireBoundary = waste-fire-boundary
  true true true true false false
