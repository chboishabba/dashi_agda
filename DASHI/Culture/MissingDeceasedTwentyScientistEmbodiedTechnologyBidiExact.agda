module DASHI.Culture.MissingDeceasedTwentyScientistEmbodiedTechnologyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistScienceCapabilityBidiExact as B
import DASHI.Culture.MissingDeceasedTwentyScientistScienceFiniteWitnessBidiExact as F

------------------------------------------------------------------------
-- EMBODIED TECHNOLOGY BIDI
--
-- An abstract benign research/engineering platform that can host the twenty
-- independent science fibres. It is a design-space object, not evidence that
-- the roster collaborated or that any historical integrated system existed.
------------------------------------------------------------------------

data EmbodiedSubsystemRole : Set where
  plasmaModel
  harshEnvironmentPowerControl
  molecularDiagnostics
  oxygenServiceMaterials
  astronomicalInference
  planetaryCharacterisation
  resilientStructureControl
  acceleratorDiagnostics
  chemicalBiologyAssays
  anomalousForceDiscrimination
  precisionForceMetrology
  hardwareVerification
  robustDecisionSupport
  thermalProtection
  dataSecurityGovernance
  spaceWeatherForecasting
  autonomousMobility
  photochemicalControl
  adaptiveStructuralWaves
  highSpeedFlowControl : EmbodiedSubsystemRole

data CompositeApplication : Set where
  longDurationSciencePlatform
  extremeEnvironmentResearchTestbed
  autonomousRemoteSurveyPlatform
  multiDomainResearchLaboratory : CompositeApplication

record EmbodiedTechnologySlot : Set where
  constructor embodied-technology-slot
  field
    person : String
    fibre : B.ScientistTechnologyFibre
    role : EmbodiedSubsystemRole
    intendedRole : String
    boundedPossibleRole : String
    finiteOrStrongerScience : Bool
    identityOrAuthorshipGated : Bool
    finiteWitnessReference : String
    reverseLeaf : String

open EmbodiedTechnologySlot public

nunoSlot = embodied-technology-slot
  "Nuno F. G. Loureiro" B.nunoLoureiroFibre plasmaModel
  "reduced-kinetic plasma simulation and reconnection/turbulence modelling"
  "magnetised-plasma modelling component for a high-power research platform"
  true false
  "existing KREHM/Hermite/plasmoid finite owners"
  "source-weld Viriato benchmark/runtime and repository/state successor"

leblancSlot = embodied-technology-slot
  "Joshua Kyle LeBlanc" B.joshuaLeBlancFibre harshEnvironmentPowerControl
  "fission-surface-power instrumentation, diagnostics and autonomous control maturation"
  "radiation/temperature-tolerant controls for long-duration high-power research systems"
  true false
  "LeBlancFSPICFiniteWitnessExact"
  "device-level qualification/failure evidence plus TechMat handover"

maiwaldSlot = embodied-technology-slot
  "Frank W. Maiwald" B.frankMaiwaldFibre molecularDiagnostics
  "cryogenic tagged-ion molecular/isomer discrimination"
  "trace molecular diagnostics for planetary/laboratory science payloads"
  true false
  "MaiwaldActionSpectroscopyFiniteWitnessExact"
  "replace synthetic action bins with source spectrum/calibration and recover data custody"

rezaSlot = embodied-technology-slot
  "Monica Jacinto / Monica Reza" B.monicaRezaFibre oxygenServiceMaterials
  "burn-resistant high-strength oxygen-service materials"
  "extreme oxidiser/high-temperature structural or liner materials after requalification"
  true false
  "existing Reza finite tradeoff/Pareto owners"
  "source-exact descendant operating window and assignment/process custody"

grillmairSlot = embodied-technology-slot
  "Carl J. Grillmair" B.carlGrillmairFibre astronomicalInference
  "stellar-stream matched-filter detection and Galactic-structure inference"
  "weak-signal survey inference for large scientific datasets"
  true false
  "existing executable matched-filter distance-scan owner"
  "source-exact stream slice/orbit uncertainty plus map/catalogue custody"

hicksSlot = embodied-technology-slot
  "Michael David Hicks" B.michaelHicksFibre planetaryCharacterisation
  "asteroid/comet photometry and physical-property inference"
  "planetary/NEO target characterisation for remote science operations"
  true false
  "HicksSmallBodyPhotometryFiniteWitnessExact"
  "replace synthetic lightcurve with source dataset/geometry and recover reduction custody"

mccaslandSlot = embodied-technology-slot
  "William Neil McCasland" B.williamNeilMcCaslandFibre resilientStructureControl
  "fault-tolerant sensor/actuator placement for flexible structures"
  "resilient control of large flexible scientific platforms/observatories"
  true false
  "existing executable Gramian/failure-family finite engine"
  "source-weld historical beam parameters and event-time programme role"

chavezSlot = embodied-technology-slot
  "Anthony Chavez" B.anthonyChavezFibre acceleratorDiagnostics
  "DARHT/Scorpius pulsed-accelerator engineering carrier"
  "high-energy radiographic diagnostics/test infrastructure"
  false true
  "science owner exists, but missing-person inheritance is identity-gated"
  "same-person weld before deeper subsystem/calibration embodiment"

thomasSlot = embodied-technology-slot
  "Jason R. Thomas" B.jasonThomasFibre chemicalBiologyAssays
  "STING and ferritinophagy signalling/target-deconvolution assays"
  "mechanistic biomarker/target-discovery assays in a research laboratory"
  true false
  "JasonThomasSignallingFiniteWitnessExact"
  "replace synthetic assay counts with source assay/target-validation data and recover lab custody"

amySlot = embodied-technology-slot
  "Amy Eskridge" B.amyEskridgeFibre anomalousForceDiscrimination
  "compare and experimentally discriminate claimed engineered-gravity mechanisms"
  "high-sensitivity anomalous-force null/comparator testbed"
  false true
  "programme/mechanism owner only; Amy-authored technical object unresolved"
  "recover Amy-authored/recorded equations or apparatus plus NF-1676/EDAA handover"

ningSlot = embodied-technology-slot
  "Ning Li" B.ningLiFibre precisionForceMetrology
  "test superconducting-gravity predictions and establish source-bounded constraints"
  "precision weak-force/null-test metrology and confounder discrimination"
  true false
  "NingLiYBCOApparatusComparisonFiniteWitnessExact"
  "later apparatus identity and Army SOW/closeout continuity"

chenSlot = embodied-technology-slot
  "Chen Shuming" B.chenShumingFibre hardwareVerification
  "simulation-based graph-specification hardware verification"
  "assurance/verification for custom processors in safety-critical research systems"
  true false
  "ChenShumingGraphHardwareVerificationFiniteWitnessExact"
  "replace synthetic counts with source graph/stimuli/coverage and recover processor responsibility"

fengSlot = embodied-technology-slot
  "Feng Yanghe" B.fengYangheFibre robustDecisionSupport
  "robust Bayesian/noisy-label classification and separately wargame decision-agent science"
  "noise-robust decision support for non-military research/operations data"
  true false
  "FengYangheClassificationFiniteWitnessExact"
  "source-exact classifier replay plus independent War Skull software/custody weld"

zhouSlot = embodied-technology-slot
  "Zhou Guangyuan" B.zhouGuangyuanFibre thermalProtection
  "low-shrinkage high-temperature polyimide-aerogel insulation"
  "lightweight thermal protection for scientific instrumentation after qualification"
  true false
  "ZhouGuangyuanPolyimideAerogelFiniteWitnessExact"
  "multi-sample process/property table plus patent/process/enterprise custody"

liuSlot = embodied-technology-slot
  "Liu Donghao" B.liuDonghaoFibre dataSecurityGovernance
  "DSMM lifecycle-wide data-security maturity governance"
  "governance layer for distributed scientific/engineering data pipelines"
  true false
  "LiuDonghaoDSMMFiniteWitnessExact"
  "source-authored rubric/scoring and dated governance/project succession"

zhangXiaoxinSlot = embodied-technology-slot
  "Zhang Xiaoxin" B.zhangXiaoxinFibre spaceWeatherForecasting
  "non-recurrent geomagnetic-storm forecasting and space-weather monitoring"
  "mission-risk/environment forecast input for long-duration science operations"
  true false
  "ZhangXiaoxinGeomagneticForecastFiniteWitnessExact"
  "source dataset/parameters/metrics plus dated NSMC/Fengyun successor"

zhangDaibingSlot = embodied-technology-slot
  "Zhang Daibing" B.zhangDaibingFibre autonomousMobility
  "UAV localisation, guidance, landing, path-following and formation control"
  "autonomous remote inspection/science mobility after mission-specific validation"
  true false
  "ZhangDaibingUAVControlFiniteWitnessExact"
  "one source-exact control replay plus project/code custodian"

liMinyongSlot = embodied-technology-slot
  "Li Minyong" B.liMinyongFibre photochemicalControl
  "photopharmacology and fluorescent molecular target visualisation"
  "externally controlled molecular research assays and diagnostics"
  true false
  "LiMinyongPhotopharmacologyFiniteWitnessExact"
  "one source-exact molecule/probe witness plus lab/project/patent custody"

fangSlot = embodied-technology-slot
  "Fang Daining" B.fangDainingFibre adaptiveStructuralWaves
  "inverse-design elastic metamaterials with prescribed modes/dispersion"
  "adaptive vibration/wave-control structures for scientific instrumentation"
  true false
  "FangDainingInverseDesignFiniteWitnessExact"
  "source energy functional/geometry/band structure plus BIT project handover"

yanSlot = embodied-technology-slot
  "Yan Hong" B.yanHongFibre highSpeedFlowControl
  "thermal/plasma flow-control science for high-speed inlet interactions"
  "high-speed flow/thermal-control research test section"
  true false
  "YanHongThermalExcitationFiniteWitnessExact"
  "source heat-release/geometry/response values plus NPU project successor"

twentyScientistEmbodiedTechnologySlots : List EmbodiedTechnologySlot
twentyScientistEmbodiedTechnologySlots =
  nunoSlot ∷ leblancSlot ∷ maiwaldSlot ∷ rezaSlot ∷ grillmairSlot ∷ hicksSlot ∷
  mccaslandSlot ∷ chavezSlot ∷ thomasSlot ∷ amySlot ∷ ningSlot ∷ chenSlot ∷
  fengSlot ∷ zhouSlot ∷ liuSlot ∷ zhangXiaoxinSlot ∷ zhangDaibingSlot ∷
  liMinyongSlot ∷ fangSlot ∷ yanSlot ∷ []

twentyScientistEmbodiedTechnologySlotCount : Nat
twentyScientistEmbodiedTechnologySlotCount = 20

finiteOrStrongerScienceSlotCount : Nat
finiteOrStrongerScienceSlotCount = 18

identityOrAuthorshipGatedSlotCount : Nat
identityOrAuthorshipGatedSlotCount = 2

requiredRoles : CompositeApplication → List EmbodiedSubsystemRole
requiredRoles longDurationSciencePlatform =
  plasmaModel ∷ harshEnvironmentPowerControl ∷ molecularDiagnostics ∷
  oxygenServiceMaterials ∷ astronomicalInference ∷ planetaryCharacterisation ∷
  resilientStructureControl ∷ thermalProtection ∷ dataSecurityGovernance ∷
  spaceWeatherForecasting ∷ autonomousMobility ∷ adaptiveStructuralWaves ∷ []
requiredRoles extremeEnvironmentResearchTestbed =
  harshEnvironmentPowerControl ∷ oxygenServiceMaterials ∷ acceleratorDiagnostics ∷
  precisionForceMetrology ∷ hardwareVerification ∷ thermalProtection ∷
  adaptiveStructuralWaves ∷ highSpeedFlowControl ∷ []
requiredRoles autonomousRemoteSurveyPlatform =
  astronomicalInference ∷ planetaryCharacterisation ∷ resilientStructureControl ∷
  hardwareVerification ∷ robustDecisionSupport ∷ dataSecurityGovernance ∷
  spaceWeatherForecasting ∷ autonomousMobility ∷ []
requiredRoles multiDomainResearchLaboratory =
  molecularDiagnostics ∷ chemicalBiologyAssays ∷ anomalousForceDiscrimination ∷
  precisionForceMetrology ∷ photochemicalControl ∷ hardwareVerification ∷
  dataSecurityGovernance ∷ []

reverseNeedsFor : CompositeApplication → List String
reverseNeedsFor longDurationSciencePlatform =
  "power/control qualification" ∷ "thermal/material operating windows" ∷
  "instrument calibration" ∷ "autonomy validation" ∷ "environment forecast validation" ∷
  "data-governance integration" ∷ "successor/custody receipts" ∷ []
reverseNeedsFor extremeEnvironmentResearchTestbed =
  "test geometry" ∷ "calibration state" ∷ "failure history" ∷
  "material qualification" ∷ "diagnostic validation" ∷ "flow-control operating window" ∷ []
reverseNeedsFor autonomousRemoteSurveyPlatform =
  "sensor/actuator geometry" ∷ "navigation/control validation" ∷
  "processor verification" ∷ "survey calibration" ∷ "forecast uncertainty" ∷
  "data-security workflow" ∷ []
reverseNeedsFor multiDomainResearchLaboratory =
  "spectroscopy calibration" ∷ "assay validation" ∷ "precision null-test controls" ∷
  "molecular probe calibration" ∷ "hardware/data provenance" ∷ []

record EmbodiedTechnologyBidi : Set where
  constructor embodied-technology-bidi
  field
    slots : List EmbodiedTechnologySlot
    intendedCompositeApplications : List CompositeApplication
    possibleCompositeApplications : List CompositeApplication
    boundedReading : String

open EmbodiedTechnologyBidi public

embodiedTwentyScientistResearchPlatform : EmbodiedTechnologyBidi
embodiedTwentyScientistResearchPlatform = embodied-technology-bidi
  twentyScientistEmbodiedTechnologySlots
  (longDurationSciencePlatform ∷ extremeEnvironmentResearchTestbed ∷ multiDomainResearchLaboratory ∷ [])
  (autonomousRemoteSurveyPlatform ∷ [])
  "Abstract benign capability-design surface. It composes technical interfaces only; historical collaboration, programme identity, deployment and event causation require independent evidence."

possibleCompositeUseImpliesHistoricalSystem : Bool
possibleCompositeUseImpliesHistoricalSystem = false

embodimentImpliesRosterCollaboration : Bool
embodimentImpliesRosterCollaboration = false

finiteMechanismImpliesOperationalQualification : Bool
finiteMechanismImpliesOperationalQualification = false

finiteMechanismImpliesPersonPossession : Bool
finiteMechanismImpliesPersonPossession = false

sourceBackedScienceImpliesEventCause : Bool
sourceBackedScienceImpliesEventCause = false

reverseApplicationQueryCanRefineAcquisition : Bool
reverseApplicationQueryCanRefineAcquisition = true
