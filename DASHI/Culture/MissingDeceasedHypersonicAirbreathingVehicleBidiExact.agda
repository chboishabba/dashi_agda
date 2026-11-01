module DASHI.Culture.MissingDeceasedHypersonicAirbreathingVehicleBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T
import DASHI.Core.RealObjectApplicationBidiExact as R
import DASHI.Physics.Aerospace.YanHongHypersonicFlowControlBidiExact as Yan
import DASHI.Physics.Materials.FangDainingActiveMechanicalMetamaterialBidiExact as Fang
import DASHI.Physics.Materials.ZhouGuangyuanPolyimideAerogelBidiExact as Zhou
import DASHI.Physics.Materials.RezaBurnResistantAlloyBidiExact as Reza
import DASHI.Control.McCaslandFaultTolerantFlexibleStructureControlBidiExact as McCasland
import DASHI.ComputerScience.ChenShumingGraphHardwareVerificationBidiExact as Chen
import DASHI.Control.ZhangDaibingUAVControlBidiExact as Zhang

------------------------------------------------------------------------
-- HYPERSONIC AIR-BREATHING RESEARCH VEHICLE / SCRAMJET TEST PLATFORM
--
-- The engineering object is sourced independently of the twenty-scientist
-- roster. Scientist fibres are mapped into subsystem requirements afterwards.
-- This is a benign research/test-platform model and does not encode a weapon or
-- a historical common programme.
------------------------------------------------------------------------

data HypersonicSubsystem : Set where
  inletCompression : HypersonicSubsystem
  isolatorShockTrain : HypersonicSubsystem
  shockBoundaryLayerControl : HypersonicSubsystem
  supersonicCombustion : HypersonicSubsystem
  hotStructuralMechanics : HypersonicSubsystem
  thermalProtection : HypersonicSubsystem
  sensingActuation : HypersonicSubsystem
  faultTolerantControl : HypersonicSubsystem
  hardwareVerification : HypersonicSubsystem
  guidanceAutonomy : HypersonicSubsystem
  highEnthalpyQualification : HypersonicSubsystem

------------------------------------------------------------------------
-- Attributed external engineering/science source atlas.
------------------------------------------------------------------------

nasaScramjetSource : Source.AttributedSource
nasaScramjetSource = Source.mkNoDOISource
  "NASA Glenn Research Center"
  "Scramjet Propulsion"
  "Beginner's Guide to Aeronautics"
  "2021-current web manifestation"
  "https://www.grc.nasa.gov/WWW/BGH/scramjet.html"
  Source.institutionalSource
  "Pays the air-breathing/supersonic-combustion distinction and X-43A rocket-boost-to-scramjet demonstration context; not a design specification."
  Source.publicAttribution

nasaInletSource : Source.AttributedSource
nasaInletSource = Source.mkNoDOISource
  "NASA Glenn Research Center"
  "Inlets"
  "Beginner's Guide to Aeronautics"
  "2021-current web manifestation"
  "https://www.grc.nasa.gov/WWW/BGH/inlet.html"
  Source.institutionalSource
  "Pays high stagnation temperature, hot boundary layers and hypersonic inlet compression context; not air-liquefaction authority."
  Source.publicAttribution

nasaLiquidRocketSource : Source.AttributedSource
nasaLiquidRocketSource = Source.mkNoDOISource
  "NASA Glenn Research Center"
  "Liquid Rocket Engine"
  "Beginner's Guide to Aeronautics"
  "current web manifestation"
  "https://www1.grc.nasa.gov/beginners-guide-to-aeronautics/liquid-rocket-engine/"
  Source.institutionalSource
  "Pays stored fuel plus stored oxidizer pumped to a combustion chamber; distinguishes rocket propellant supply from scramjet atmospheric-air ingestion."
  Source.publicAttribution

yanThermalSource : Source.AttributedSource
yanThermalSource = Source.mkDOISource
  "Yan Hong; Wang Song"
  "Control of shock/boundary layer interaction in supersonic inlet using thermal excitation"
  "Acta Aerodynamica Sinica 32(6)"
  "2014"
  "10.7638/kqdlxxb-2013.0102"
  "https://kqdlxxb.xml-journal.net/article/doi/10.7638/kqdlxxb-2013.0102"
  Source.academicArticleSource
  "Pays a direct Mach-5 inlet/SBLI thermal-excitation science interface; does not pay a historical vehicle programme."
  Source.publicAttribution

zhouAerogelSource : Source.AttributedSource
zhouAerogelSource = Source.mkDOISource
  "Zhou Guangyuan et al."
  "Low-shrinkage high-temperature polyimide aerogel study"
  "Chemical Engineering Journal"
  "2023"
  "10.1016/j.cej.2023.147642"
  "https://doi.org/10.1016/j.cej.2023.147642"
  Source.academicArticleSource
  "Pays source-exact thermal/structure-property coordinates for a lightweight insulation candidate; not hypersonic qualification."
  Source.publicAttribution

chenVerificationSource : Source.AttributedSource
chenVerificationSource = Source.mkDOISource
  "Shuming Chen et al."
  "Simulation-Based Hardware Verification with a Graph-Based Specification"
  "2018 journal article"
  "2018"
  "10.1155/2018/6398616"
  "https://doi.org/10.1155/2018/6398616"
  Source.academicArticleSource
  "Pays a reusable hardware-verification method; processor/vehicle instantiation remains unpaid."
  Source.publicAttribution

rezaAlloySource : Source.AttributedSource
rezaAlloySource = Source.mkNoDOISource
  "Monica A. Jacinto; Dallis A. Hardwick"
  "Burn-resistant and high tensile strength metal alloys"
  "US patent family US20030053926A1 / US20040208777A1 / US20100266442A1"
  "2003-2010 manifestations"
  "https://patents.google.com/patent/US20100266442A1/en"
  (Source.namedSourceKind "patent")
  "Pays high-pressure oxygen-service alloy/process/test coordinates and rocket-propulsion motivation; transfer to atmospheric hypersonic service requires new qualification."
  Source.publicAttribution

fangExtremeEnvironmentSource : Source.AttributedSource
fangExtremeEnvironmentSource = Source.mkNoDOISource
  "Beijing Institute of Technology, Institute of Advanced Structure Technology"
  "Ultra-high-temperature extreme-environment mechanical/material testing progress"
  "BIT institutional research page"
  "2016"
  "BIT institutional source retained in FangDainingActiveMechanicalMetamaterialBidiExact"
  Source.institutionalSource
  "Pays oxidising/inert ultra-high-temperature structural and thermal-shock test capability; not a scramjet-specific material qualification."
  Source.publicAttribution

mccaslandPlacementSource : Source.AttributedSource
mccaslandPlacementSource = Source.mkNoDOISource
  "William Neil McCasland"
  "Fault-Tolerant Sensor and Actuator Selection for Control of Flexible Structures"
  "1989 American Control Conference / AFIT thesis"
  "1989"
  "NASA/NTIS index A89-54007 / AD-A217384"
  Source.academicArticleSource
  "Pays controllability/observability-Gramian fault-tolerant placement method; hypersonic plant instantiation requires a new system model and failure set."
  Source.publicAttribution

zhangControlSource : Source.AttributedSource
zhangControlSource = Source.mkDOISource
  "Zhang Daibing et al."
  "UAV guidance/localisation/control publication family representative"
  "source publication family"
  "2017-2018"
  "10.13700/j.bh.1001-5965.2016.0679"
  "https://doi.org/10.13700/j.bh.1001-5965.2016.0679"
  Source.academicArticleSource
  "Pays a source-backed vehicle guidance/control method family; hypersonic dynamics, sensors and gains require separate qualification."
  Source.publicAttribution

hypersonicSourceAtlas : Source.AttributedSourceAtlas
hypersonicSourceAtlas = Source.mkSourceAtlas
  "hypersonic air-breathing real-object source atlas"
  "DASHI.Culture.MissingDeceasedHypersonicAirbreathingVehicleBidiExact"
  (nasaScramjetSource ∷ nasaInletSource ∷ nasaLiquidRocketSource ∷ yanThermalSource ∷
   zhouAerogelSource ∷ chenVerificationSource ∷ rezaAlloySource ∷
   fangExtremeEnvironmentSource ∷ mccaslandPlacementSource ∷ zhangControlSource ∷ [])
  "Engineering requirements and bounded scientist-to-subsystem interfaces only; citation imports neither proof, historical participation, common programme nor event cause."

------------------------------------------------------------------------
-- Real-object requirements.  Reverse targets preserve the missing application
-- geometry / calibration / process / qualification coordinates.
------------------------------------------------------------------------

inletRequirement : R.RealObjectRequirement
inletRequirement = R.mkRequirement
  "inlet/SBLI"
  "compress and condition hypersonic atmospheric flow while controlling shock/boundary-layer interaction and avoiding unacceptable separation/unstart regimes"
  "NASA hypersonic inlet context; Yan DOI 10.7638/kqdlxxb-2013.0102"
  (T.acquireApplicationGeometry ∷ T.acquireOperatingWindow ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ [])
  "Source-level inlet physics does not determine a flight-qualified inlet geometry or control law."

combustionRequirement : R.RealObjectRequirement
combustionRequirement = R.mkRequirement
  "supersonic combustion/mixing"
  "mix fuel with ingested high-speed air and release heat while the scramjet combustor flow remains supersonic"
  "NASA Scramjet Propulsion"
  (T.acquireApplicationGeometry ∷ T.acquireOperatingWindow ∷ T.acquireValidationCorpus ∷ T.acquireQualificationEvidence ∷ [])
  "No retained scientist is promoted here merely from adjacent materials/control science."

hotStructureRequirement : R.RealObjectRequirement
hotStructureRequirement = R.mkRequirement
  "hot structural mechanics"
  "retain structural integrity under high-temperature oxidising/inert, mechanical and thermal-shock loading"
  "BIT Fang extreme-environment testing plus NASA hypersonic thermal context"
  (T.acquireConstitutiveConfiguration ∷ T.acquireOperatingWindow ∷ T.acquireFailureHistory ∷ T.acquireQualificationEvidence ∷ [])
  "Extreme-environment testing transfers as an engineering interface; vehicle material/geometry qualification remains separate."

thermalProtectionRequirement : R.RealObjectRequirement
thermalProtectionRequirement = R.mkRequirement
  "thermal protection / insulation"
  "provide lightweight thermal-management material performance under source-specific hypersonic heat/cycling/erosion loads"
  "Zhou DOI 10.1016/j.cej.2023.147642 plus NASA high-temperature inlet context"
  (T.acquireConstitutiveConfiguration ∷ T.acquireOperatingWindow ∷ T.acquireFailureHistory ∷ T.acquireQualificationEvidence ∷ [])
  "A 200 C conductivity datum and polymer stability coordinates do not qualify a TPS for hypersonic flight."

oxidisingMaterialRequirement : R.RealObjectRequirement
oxidisingMaterialRequirement = R.mkRequirement
  "oxidising hot-section materials"
  "retain strength/oxidation/burn resistance in a candidate hot oxidising propulsion environment"
  "Jacinto/Hardwick oxygen-service alloy patent family"
  (T.acquireConstitutiveConfiguration ∷ T.acquireOperatingWindow ∷ T.acquireFailureHistory ∷ T.acquireQualificationEvidence ∷ T.acquireTacitExecutionKnowledge ∷ [])
  "High-pressure gaseous-oxygen rocket service is not atmospheric scramjet service; fuel/air chemistry, heat flux, stress state and lifecycle require new tests."

faultControlRequirement : R.RealObjectRequirement
faultControlRequirement = R.mkRequirement
  "fault-tolerant sensing/actuation"
  "choose and reconfigure sensors/actuators while retaining observability/controllability across declared failure sets"
  "McCasland 1989 ACC/thesis"
  (T.acquireApplicationGeometry ∷ T.acquireFailureHistory ∷ T.acquireValidationCorpus ∷ T.acquireIntegrationWorkflow ∷ [])
  "Method transfer requires a hypersonic vehicle state-space/structural model, candidate sites and failure family."

hardwareVerificationRequirement : R.RealObjectRequirement
hardwareVerificationRequirement = R.mkRequirement
  "digital control-hardware verification"
  "verify complex flight/engine/sensor-processing digital hardware against an explicit specification and validation corpus"
  "Chen DOI 10.1155/2018/6398616"
  (T.acquireValidationCorpus ∷ T.acquireFailureHistory ∷ T.acquireQualificationEvidence ∷ T.acquireIntegrationWorkflow ∷ [])
  "Graph-verification method does not identify or qualify any particular hypersonic processor."

guidanceRequirement : R.RealObjectRequirement
guidanceRequirement = R.mkRequirement
  "guidance/autonomy"
  "perform vehicle-state estimation, guidance and closed-loop autonomous control under a vehicle-specific dynamics/sensor/environment model"
  "Zhang Daibing DOI publication family"
  (T.acquireApplicationGeometry ∷ T.acquireCalibrationState ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireIntegrationWorkflow ∷ [])
  "UAV control methods transfer only after vehicle-specific dynamics, gains, sensing, robustness and flight-test qualification."

qualificationRequirement : R.RealObjectRequirement
qualificationRequirement = R.mkRequirement
  "high-enthalpy ground qualification"
  "validate subsystem response across the intended aerothermal, structural and propulsion operating envelope"
  "NASA hypersonic inlet/test context"
  (T.acquireOperatingWindow ∷ T.acquireFailureHistory ∷ T.acquireQualificationEvidence ∷ T.acquireValidationCorpus ∷ [])
  "A collection of component papers is not an integrated vehicle qualification campaign."

hypersonicRealObject : R.RealEngineeringObject
hypersonicRealObject = R.real-engineering-object
  "advanced air-breathing hypersonic research vehicle / scramjet test platform"
  "benign aerospace research/test object"
  hypersonicSourceAtlas
  (inletRequirement ∷ combustionRequirement ∷ hotStructureRequirement ∷
   thermalProtectionRequirement ∷ oxidisingMaterialRequirement ∷ faultControlRequirement ∷
   hardwareVerificationRequirement ∷ guidanceRequirement ∷ qualificationRequirement ∷ [])
  "study inlet/combustion/aerothermal/control integration and subsystem qualification in a high-speed research platform"
  "Real engineering object, not evidence the retained scientists collaborated on one vehicle and not a weapon-programme classification."

------------------------------------------------------------------------
-- Seven low-invention scientist/subsystem fits.
------------------------------------------------------------------------

yanHongFit : R.ScientistObjectFit
yanHongFit = R.mkFit
  "Yan Hong"
  "DASHI.Physics.Aerospace.YanHongHypersonicFlowControlBidiExact"
  "Mach-5 thermal-excitation inlet/SBLI control"
  inletRequirement R.directSourceFit
  "DOI 10.7638/kqdlxxb-2013.0102"
  "Direct source fit: the retained work is itself a supersonic inlet shock/boundary-layer control study."
  "acquire exact response curves, mesh/boundary conditions, heat-source model and vehicle/inlet qualification envelope"
  false
  "Direct technical fit does not establish participation in any historical hypersonic vehicle programme."

fangDainingFit : R.ScientistObjectFit
fangDainingFit = R.mkFit
  "Fang Daining"
  "DASHI.Physics.Materials.FangDainingActiveMechanicalMetamaterialBidiExact"
  "ultra-high-temperature oxidising/inert mechanical and thermal-shock test capability"
  hotStructureRequirement R.engineeringTransfer
  "BIT ultra-high-temperature extreme-environment testing source"
  "Engineering transfer: extreme-environment structural testing is directly relevant, but the retained source is not a scramjet component qualification."
  "acquire candidate vehicle material/geometry, load/heat-flux history, cycling and failure/qualification evidence"
  false
  "Aerospace/defence applicability does not identify a particular vehicle or programme."

zhouGuangyuanFit : R.ScientistObjectFit
zhouGuangyuanFit = R.mkFit
  "Zhou Guangyuan"
  "DASHI.Physics.Materials.ZhouGuangyuanPolyimideAerogelBidiExact"
  "low-shrinkage high-temperature polyimide-aerogel thermal insulation"
  thermalProtectionRequirement R.engineeringTransfer
  "DOI 10.1016/j.cej.2023.147642"
  "Engineering transfer: low conductivity/lightweight thermal material coordinates nominate a TPS/insulation candidate only."
  "acquire thermal cycling, ablation/erosion response, attachment geometry, higher-temperature window and hypersonic qualification"
  false
  "A source-exact 200 C material datum does not create hypersonic qualification or historical participation."

monicaRezaFit : R.ScientistObjectFit
monicaRezaFit = R.mkFit
  "Monica Jacinto / Monica Reza"
  "DASHI.Physics.Materials.RezaBurnResistantAlloyBidiExact"
  "Ni-Co-Cr-Al-Ti high-pressure oxygen-service burn/strength process window"
  oxidisingMaterialRequirement R.engineeringTransfer
  "US20030053926A1 / US20040208777A1 / downstream MONDALOY lineage"
  "Engineering transfer: hot oxidising propulsion materials are relevant, but rocket oxygen-service chemistry is not identical to atmospheric scramjet service."
  "requalify composition/process/microstructure against hot-air/fuel chemistry, wall heat flux, stress state, oxidation, erosion and lifecycle"
  false
  "MONDALOY lineage does not establish use in a scramjet or any common retained-scientist hypersonic programme."

mccaslandFit : R.ScientistObjectFit
mccaslandFit = R.mkFit
  "William Neil McCasland"
  "DASHI.Control.McCaslandFaultTolerantFlexibleStructureControlBidiExact"
  "Gramian-based sensor/actuator placement and explicit failure coverage"
  faultControlRequirement R.methodTransfer
  "1989 ACC / AFIT thesis / NASA index A89-54007"
  "Method transfer: fault-tolerant placement mathematics can be applied to a hypersonic plant once its state-space model and failure family are supplied."
  "acquire vehicle dynamics, candidate sensors/actuators, scaled Gramians, protected failures and reconfiguration policy"
  false
  "Method compatibility does not establish that the method was used on a historical hypersonic system."

chenShumingFit : R.ScientistObjectFit
chenShumingFit = R.mkFit
  "Chen Shuming"
  "DASHI.ComputerScience.ChenShumingGraphHardwareVerificationBidiExact"
  "graph-specification simulation-based hardware verification"
  hardwareVerificationRequirement R.methodTransfer
  "DOI 10.1155/2018/6398616"
  "Method transfer: target-specific flight/control hardware could consume the verification method after a processor specification and validation corpus exist."
  "acquire target graph semantics, stimulus corpus, coverage metric, mismatch oracle and hardware qualification receipt"
  false
  "Publication and NUDT affiliation do not establish a hypersonic processor or programme."

zhangDaibingFit : R.ScientistObjectFit
zhangDaibingFit = R.mkFit
  "Zhang Daibing"
  "DASHI.Control.ZhangDaibingUAVControlBidiExact"
  "guidance/localisation/control method family"
  guidanceRequirement R.methodTransfer
  "DOI 10.13700/j.bh.1001-5965.2016.0679 and related source family"
  "Method transfer: vehicle-level sensing/guidance/control structure is reusable, but dynamics and qualification are object-specific."
  "acquire hypersonic dynamics/state definition, sensors, control law/gains, test geometry and robustness metrics"
  false
  "UAV publications do not establish control of a Mach-5 vehicle or common programme membership."

strongHypersonicFits : List R.ScientistObjectFit
strongHypersonicFits =
  yanHongFit ∷ fangDainingFit ∷ zhouGuangyuanFit ∷ monicaRezaFit ∷
  mccaslandFit ∷ chenShumingFit ∷ zhangDaibingFit ∷ []

------------------------------------------------------------------------
-- Reused in-repo science objects: these aliases make the weld executable at
-- source level rather than relying on prose similarity.
------------------------------------------------------------------------

yanDirectReceipt : Yan.YanHongWorkReceipt
yanDirectReceipt = Yan.thermalExcitationMach5Receipt

fangExtremeEnvironmentReceipt : Fang.ExtremeEnvironmentMaterialsScience
fangExtremeEnvironmentReceipt = Fang.fangUltraHighTemperatureTesting

zhouThermalCarrier = Zhou.zhouAerogelCarrier

rezaOxygenExample : Reza.TestedAlloyExample
rezaOxygenExample = Reza.example1

mccaslandPlacementMeasure : McCasland.GramianPerformanceMeasure
mccaslandPlacementMeasure = McCasland.observabilityGramianMeasure

chenVerificationCarrier = Chen.chenVerificationCarrier

zhangControlCarrier = Zhang.zhangDaibingControlCarrier

------------------------------------------------------------------------
-- Thermodynamic and investigation firewalls.
------------------------------------------------------------------------

inletCompressionPaysAirLiquefaction : Bool
inletCompressionPaysAirLiquefaction = false

scramjetCarriesOxidizerLikeRocket : Bool
scramjetCarriesOxidizerLikeRocket = false

rocketAndScramjetAreSameThermodynamicObject : Bool
rocketAndScramjetAreSameThermodynamicObject = false

rocketBoostPlusScramjetCruiseCanCoexist : Bool
rocketBoostPlusScramjetCruiseCanCoexist = true

oxygenServiceAlloyPaysScramjetQualification : Bool
oxygenServiceAlloyPaysScramjetQualification = false

hypersonicRelevancePaysWeaponProgramme : Bool
hypersonicRelevancePaysWeaponProgramme = false

subsystemFitPaysHistoricalParticipation : Bool
subsystemFitPaysHistoricalParticipation = R.subsystemFitPaysHistoricalParticipation

multipleFitsPayCommonProgramme : Bool
multipleFitsPayCommonProgramme = R.multipleFitsPayCommonProgramme

realObjectFitPaysEventCause : Bool
realObjectFitPaysEventCause = R.realObjectFitPaysEventCause

realObjectFitPaysH2 : Bool
realObjectFitPaysH2 = R.realObjectFitPaysH2

normalScramjetCompressionHeatsRatherThanLiquefiesAir : Bool
normalScramjetCompressionHeatsRatherThanLiquefiesAir = true
