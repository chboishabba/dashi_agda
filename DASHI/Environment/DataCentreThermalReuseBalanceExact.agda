module DASHI.Environment.DataCentreThermalReuseBalanceExact where

-- Energy-quantity and source-grade boundary for data-centre thermal reuse.
-- 2026-10-24. Illustrative integer kW witness, NOT a surveyed project.
-- Distinguishes heat REUSED from heat CREATED by compressor electricity.
-- The older noise/EM evidence owner remains independent.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Environment.DataCentreAcousticExposureAttributionExact as Acoustic
import DASHI.Planning.DataCentreUrbanResourceConflictExact as Planning

data ThermalRoute : Set where
  directLowTemperatureReuse : ThermalRoute
  compressorHeatPumpUpgrade : ThermalRoute
  heatDrivenAbsorptionCooling : ThermalRoute
  thermalStorageAndCascading : ThermalRoute
  residualAmbientRejection : ThermalRoute

data Offtaker : Set where
  aquaticCentre : Offtaker
  commercialHotWaterPreheat : Offtaker
  foodAndBeverageProcess : Offtaker
  agricultureAquaculture : Offtaker
  municipalHeating : Offtaker
  coolingOrDehumidification : Offtaker

data EvidenceStanding : Set where
  namedOperationalDeployment : EvidenceStanding
  supplierReportedPerformance : EvidenceStanding
  peerReviewedSimulation : EvidenceStanding
  peerReviewedReview : EvidenceStanding
  officialReport : EvidenceStanding
  demonstrationOrProposal : EvidenceStanding

record HeatSourceReceipt : Set where
  constructor heatSourceReceipt
  field
    authorOrInstitution : String
    datedTitle : String
    sourceURI : String
    grade : EvidenceStanding
    groundedScope : String
    notEstablished : String

fortum2026 : HeatSourceReceipt
fortum2026 = heatSourceReceipt
  "Fortum"
  "Heat production started at two large data-centre sites (2026-05-06)"
  "https://www.fortum.com/media/2026/05/fortum-has-started-heat-production-two-large-data-centre-sites-finland"
  namedOperationalDeployment
  "Heat-pump sites operational using ambient air and boilers; Microsoft data-centre heat incorporation planned from 2027"
  "2026 operational date does not establish actual DC heat integration or delivered 40% of demand"

euReport2026 : HeatSourceReceipt
euReport2026 = heatSourceReceipt
  "European Commission"
  "COM(2026)500 data-centre energy efficiency (2026-09-21)"
  "https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:52026DC0500"
  officialReport
  "First reporting period estimates 1.8 percent of generated DC heat reused and 67 facilities reporting any reuse"
  "EU reporting sample does not imply identical world-wide rates or per-site economics"

guangzhouAbsorption2025 : HeatSourceReceipt
guangzhouAbsorption2025 = heatSourceReceipt
  "Applied Energy research authors"
  "Switchable multistage absorption chiller for ultra-low-grade waste heat driven cooling in data centers (2025)"
  "https://doi.org/10.1016/j.apenergy.2025.126407"
  peerReviewedSimulation
  "Triple-stage LiBr-H2O model driven by 50 Celsius heat; Guangzhou case reports 80.5 percent mechanical cooling-load reduction"
  "Case-study mechanical cooling reduction does not establish overall grid savings or real Queensland site performance"

wasteHeatReview2025 : HeatSourceReceipt
wasteHeatReview2025 = heatSourceReceipt
  "Applied Energy review authors"
  "Data centers waste heat recovery technologies: Review and evaluation (2025)"
  "https://doi.org/10.1016/j.apenergy.2025.125489"
  peerReviewedReview
  "Exergy-relative comparison of data-centre recovery methods and sources"
  "An available heat quantity does not identify economically useful heat at requested temperature"

australianGuidance2026 : HeatSourceReceipt
australianGuidance2026 = heatSourceReceipt
  "Australian Government"
  "Waste heat recovery guidance"
  "https://www.energy.gov.au/business/equipment-guides/waste-heat-recovery"
  officialReport
  "Heat pump upgrading and commercial/industrial waste-heat applications are established engineering options"
  "Guidance does not provide facility-specific verified COP, demand or capital recovery"

data OperatingMetric : Set where
  electricityPUE : OperatingMetric
  reportedHeatReuseERF : OperatingMetric
  waterUseWUE : OperatingMetric
  coolingSystemAcoustics : OperatingMetric
  processHeatDelivered : OperatingMetric
  processHeatExergy : OperatingMetric
  carbonDisplacement : OperatingMetric

-- Source-to-receptor acoustic channels and thermal engineering are complementary,
-- but a cooling retrofit cannot be assumed to reduce OUTDOOR noise without
-- measurements of dry coolers, condensers, pumps and operating schedules.
acousticOwner : Acoustic.PhysicalChannel
acousticOwner = Acoustic.airbornePressure

planningOwner : Planning.Project
planningOwner = Planning.aiDataCentre

record PhysicalSiteObligations : Set where
  constructor physicalSiteObligations
  field
    measuredITAndFacilityPower : Bool
    capturedHeatRateAndTemperature : Bool
    heatExchangerApproachAndPinch : Bool
    heatPumpCOPMapAndLift : Bool
    offTakerConcurrentHourlyDemand : Bool
    pumpAndPipelineElectricityLosses : Bool
    heatStorageRoundtripAndCapacity : Bool
    noiseSpectrumBeforeAndAfter : Bool
    evaporativeWaterAndRefrigerantAudit : Bool
    sourceMatchedCarbonCounterfactual : Bool
    actualPermitAndNetworkTariff : Bool

noSiteReceiptsPaid : PhysicalSiteObligations
noSiteReceiptsPaid =
  physicalSiteObligations false false false false false
                          false false false false false false

-- Exact illustrative balance in kW, with no refrigeration or pipe losses.
-- IT = 10000, non-IT site overhead = 2500, total site = 12500.
-- Of IT heat, 2000 goes directly to a cool incoming sink, 6000 enters
-- heat pump evaporator, and 2000 remains uncaptured.
-- HP compressor power = 2400; HP hot delivery = 8400.
-- Heat delivered = 2000+8400 = 10400.
-- Unrecovered IT + non-IT site overhead = 2000+2500 = 4500.
-- Total electric input = 12500+2400=14900; exported+ambient=14900.

itKilowatt : Nat
itKilowatt = 10000

siteOverheadKilowatt : Nat
siteOverheadKilowatt = 2500

sitePowerKilowatt : Nat
sitePowerKilowatt = itKilowatt + siteOverheadKilowatt

directReuseKilowatt : Nat
directReuseKilowatt = 2000

hpEvaporatorKilowatt : Nat
hpEvaporatorKilowatt = 6000

uncapturedITKilowatt : Nat
uncapturedITKilowatt = 2000

hpElectricKilowatt : Nat
hpElectricKilowatt = 2400

hpOutputKilowatt : Nat
hpOutputKilowatt = hpEvaporatorKilowatt + hpElectricKilowatt

totalExportKilowatt : Nat
totalExportKilowatt = directReuseKilowatt + hpOutputKilowatt

residualAmbientKilowatt : Nat
residualAmbientKilowatt = uncapturedITKilowatt + siteOverheadKilowatt

itPartitionExact :
  itKilowatt ≡ directReuseKilowatt + hpEvaporatorKilowatt + uncapturedITKilowatt
itPartitionExact = refl

hpFirstLawExact :
  hpOutputKilowatt ≡ hpEvaporatorKilowatt + hpElectricKilowatt
hpFirstLawExact = refl

wholeFacilityFirstLawExact :
  sitePowerKilowatt + hpElectricKilowatt
  ≡ totalExportKilowatt + residualAmbientKilowatt
wholeFacilityFirstLawExact = refl

copThreePointFiveExact :
  10 * hpOutputKilowatt ≡ 35 * hpElectricKilowatt
copThreePointFiveExact = refl

-- Positive electric drive invalidates the naive idea that delivered HP heat
-- is the same quantity as the captured waste-heat stream.
heatPumpDeliveryNotIdenticalToCapturedSource :
  hpOutputKilowatt ≡ hpEvaporatorKilowatt → ⊥
heatPumpDeliveryNotIdenticalToCapturedSource ()

-- Two facilities can have exactly the same available heat, but not
-- the same realised benefit: availability of a coincident thermal offtaker
-- is not encoded by the waste-heat quantity.
data DemandCase : Set where
  matchedOfftaker : DemandCase
  noConcurrentOfftaker : DemandCase

heatAvailableKilowatt : DemandCase → Nat
heatAvailableKilowatt _ = 8000

heatActuallyRecoveredKilowatt : DemandCase → Nat
heatActuallyRecoveredKilowatt matchedOfftaker = 8000
heatActuallyRecoveredKilowatt noConcurrentOfftaker = 0

sameHeatPotential :
  heatAvailableKilowatt matchedOfftaker
  ≡ heatAvailableKilowatt noConcurrentOfftaker
sameHeatPotential = refl

differentRealisedHeat :
  heatActuallyRecoveredKilowatt matchedOfftaker
  ≡ heatActuallyRecoveredKilowatt noConcurrentOfftaker → ⊥
differentRealisedHeat ()

-- Hypothetical 50 C multistage absorption example at thermal COP 0.35.
-- It uses 6000 kW of heat to provide 2100 kW of chilling and must reject
-- 8100 kW at the absorption condenser/absorber, before auxiliaries.
-- This DOES NOT prove that outdoor noise, water usage, or total energy fall.
absorptionDriveKilowatt : Nat
absorptionDriveKilowatt = 6000

absorptionChillKilowatt : Nat
absorptionChillKilowatt = 2100

absorptionRejectKilowatt : Nat
absorptionRejectKilowatt = 8100

absorptionBalanceExact :
  absorptionRejectKilowatt
  ≡ absorptionDriveKilowatt + absorptionChillKilowatt
absorptionBalanceExact = refl

absorptionCOPThirtyFiveHundredths :
  100 * absorptionChillKilowatt ≡ 35 * absorptionDriveKilowatt
absorptionCOPThirtyFiveHundredths = refl

-- No model of carbon savings, a real Queensland facility, noise reduction,
-- thermal storage dispatch, or legal compliance is proven by this witness.
