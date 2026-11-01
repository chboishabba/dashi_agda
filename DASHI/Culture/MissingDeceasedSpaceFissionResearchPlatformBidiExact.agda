module DASHI.Culture.MissingDeceasedSpaceFissionResearchPlatformBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T
import DASHI.Core.RealObjectApplicationBidiExact as R

nasaFissionSource : Source.AttributedSource
nasaFissionSource = Source.mkNoDOISource
  "NASA"
  "Fission Surface Power / space-fission power maturation"
  "NASA NTRS / TechPort institutional surfaces"
  "2025-2026 manifestations"
  "NASA FSP NTRS/TechPort surfaces retained in LeBlanc owners"
  Source.institutionalSource
  "Pays a real space-fission power research/qualification object class and harsh-environment I&C requirements; not a common programme for the retained cohort."
  Source.publicAttribution

spacePlatformSource : Source.AttributedSource
spacePlatformSource = Source.mkNoDOISource
  "DASHI source composite"
  "Long-duration autonomous space research platform requirements"
  "composition of source-backed retained science interfaces"
  "current formalisation"
  "DASHI in-repo science owners"
  (Source.namedSourceKind "formalisation composite")
  "Defines only an engineering consumer surface over separately attributed science."
  Source.publicAttribution

spaceFissionAtlas : Source.AttributedSourceAtlas
spaceFissionAtlas = Source.mkSourceAtlas
  "space/fission research-platform atlas"
  "DASHI.Culture.MissingDeceasedSpaceFissionResearchPlatformBidiExact"
  (nasaFissionSource ∷ spacePlatformSource ∷ [])
  "Object requirements are real-engineering/application coordinates; no historical common-programme claim."

powerRequirement : R.RealObjectRequirement
powerRequirement = R.mkRequirement
  "fission power and I&C"
  "generate and control long-duration power under declared radiation/thermal/failure environments"
  "NASA Fission Surface Power institutional surfaces"
  (T.acquireOperatingWindow ∷ T.acquireFailureHistory ∷ T.acquireQualificationEvidence ∷ T.acquireIntegrationWorkflow ∷ [])
  "Notional environments and component studies are not flight qualification."

spaceEnvironmentRequirement : R.RealObjectRequirement
spaceEnvironmentRequirement = R.mkRequirement
  "space environment prediction"
  "predict space-weather conditions relevant to operations, instrumentation and risk management"
  "Zhang Xiaoxin geomagnetic-forecast source lineage"
  (T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireOperatingWindow ∷ [])
  "Forecast science does not by itself determine vehicle authority or mission decisions."

thermalStructureRequirement : R.RealObjectRequirement
thermalStructureRequirement = R.mkRequirement
  "lightweight thermal/structural protection"
  "maintain thermal and structural margins for long-duration remote hardware"
  "Zhou/Fang source-backed material and mechanics owners"
  (T.acquireConstitutiveConfiguration ∷ T.acquireOperatingWindow ∷ T.acquireFailureHistory ∷ T.acquireQualificationEvidence ∷ [])
  "Material transfer requires mission-specific radiation, vacuum, cycling and structural qualification."

autonomyRequirement : R.RealObjectRequirement
autonomyRequirement = R.mkRequirement
  "autonomy and resilient control"
  "perform remote state estimation, guidance, fault accommodation and hardware verification"
  "McCasland/Chen/Zhang Daibing source-backed methods"
  (T.acquireApplicationGeometry ∷ T.acquireValidationCorpus ∷ T.acquireFailureHistory ∷ T.acquireIntegrationWorkflow ∷ [])
  "Method transfer requires a concrete plant, processor, sensor suite and failure model."

spaceFissionResearchPlatform : R.RealEngineeringObject
spaceFissionResearchPlatform = R.real-engineering-object
  "long-duration autonomous space/fission research platform"
  "benign space-science and power research object"
  spaceFissionAtlas
  (powerRequirement ∷ spaceEnvironmentRequirement ∷ thermalStructureRequirement ∷ autonomyRequirement ∷ [])
  "study long-duration power, environment, thermal/structural and autonomous-operation integration"
  "Engineering compatibility does not establish a shared historical mission or programme."

leblancFissionPowerFit : R.ScientistObjectFit
leblancFissionPowerFit = R.mkFit
  "Joshua Kyle LeBlanc"
  "DASHI LeBlanc Fission Surface Power I&C owners"
  "Fission Surface Power instrumentation/control and qualification"
  powerRequirement R.directSourceFit
  "NASA NTRS 20250008475 / FSP TechPort lineage"
  "Direct source fit to the platform's power-and-I&C subsystem."
  "recover exact post-loss TechMat roster, sensor requirements, failure/calibration matrices and qualification state"
  false
  "Direct technical participation in FSP does not establish participation in this composite platform."

zhangXiaoxinSpaceWeatherFit : R.ScientistObjectFit
zhangXiaoxinSpaceWeatherFit = R.mkFit
  "Zhang Xiaoxin"
  "DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastBidiExact"
  "geomagnetic-storm prediction and Fengyun space-weather science"
  spaceEnvironmentRequirement R.directSourceFit
  "DOI 10.1029/2023SW003522 plus retained Fengyun surfaces"
  "Direct science fit to space-environment prediction."
  "recover event-level data, exact CEEMDAN/CWT parameters, payload/calibration state and operational decision interface"
  false
  "Forecast relevance does not establish a shared platform or event cause."

zhouSpaceThermalFit : R.ScientistObjectFit
zhouSpaceThermalFit = R.mkFit
  "Zhou Guangyuan"
  "DASHI.Physics.Materials.ZhouGuangyuanPolyimideAerogelBidiExact"
  "lightweight thermal insulation candidate"
  thermalStructureRequirement R.engineeringTransfer
  "DOI 10.1016/j.cej.2023.147642"
  "Engineering transfer to a space thermal subsystem is plausible only after mission-specific qualification."
  "acquire vacuum/radiation/cycling/attachment and mission-temperature qualification"
  false
  "Candidate material fit does not establish historical use."

spaceFissionFitPaysHistoricalMission : Bool
spaceFissionFitPaysHistoricalMission = false
