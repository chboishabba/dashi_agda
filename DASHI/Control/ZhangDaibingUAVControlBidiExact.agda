module DASHI.Control.ZhangDaibingUAVControlBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificCapabilityCarrierBidiExact as C
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T

------------------------------------------------------------------------
-- ZHANG DAIBING: UAV GUIDANCE / LOCALISATION / CONTROL FAMILY
--
-- Source coordinates retained by the roster:
--   DOI 10.11887/j.cn.201801023
--   DOI 10.13700/j.bh.1001-5965.2016.0679
--   DOI 10.13973/j.cnki.robot.2017.0160
--
-- These are multiple technical objects.  The canonical pipeline below is a
-- typed synthesis of source-backed coordinates, not a claim that one deployed
-- vehicle implemented every stage or paper.
------------------------------------------------------------------------

data UAVControlStage : Set where
  stateSensing multisensorFusion localisation referenceGeneration
  guidanceCommand flightControl landingOrPathDecision formationCoordination
  fieldTestResidual : UAVControlStage

record UAVControlPipeline : Set where
  constructor uav-control-pipeline
  field
    sourceReferences : String
    capabilityFamily : String
    stages : List UAVControlStage
    intendedUse : String
    missingExecutableCoordinate : String

open UAVControlPipeline public

canonicalZhangDaibingControlPipeline : UAVControlPipeline
canonicalZhangDaibingControlPipeline = uav-control-pipeline
  "DOI 10.11887/j.cn.201801023; DOI 10.13700/j.bh.1001-5965.2016.0679; DOI 10.13973/j.cnki.robot.2017.0160"
  "autonomous landing, path following, multisensor localisation, formation and unmanned-system control"
  (stateSensing ∷ multisensorFusion ∷ localisation ∷ referenceGeneration ∷
   guidanceCommand ∷ flightControl ∷ landingOrPathDecision ∷
   formationCoordination ∷ fieldTestResidual ∷ [])
  "source-specific UAV guidance/localisation/control tasks"
  "choose one exact paper and recover state definition, dynamics, control/guidance law, gains, sensor model, test geometry and error/robustness metrics"

zhangDaibingControlCarrier : C.ScientificCapabilityCarrier
zhangDaibingControlCarrier = C.scientific-capability-carrier
  "autonomous systems control"
  "UAV guidance/localisation/control algorithm family"
  C.sourceCodeOrAlgorithm
  C.carrierPublic
  "autonomous landing/path-following/localisation/formation control"
  "three DOI-level source objects"
  "The family is public at publication level; exact fielded code, gains, sensor calibration and vehicle configuration remain application-specific."

zhangDaibingTransformation : T.ApplicationTransformation
zhangDaibingTransformation = T.application-transformation
  "autonomous UAV operation"
  (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ T.uncertaintyModel ∷ [])
  (T.applicationGeometry ∷ T.calibrationState ∷ T.failureHistory ∷
   T.validationCorpus ∷ T.integrationWorkflow ∷ [])
  "Zhang Daibing DOI publication family"
  "Operational autonomy requires vehicle/sensor geometry, calibrated state estimation, environmental assumptions, validation and failure handling."

data ZhangDaibingReverseTarget : Set where
  selectExactPaper acquireDynamics acquireStateDefinition acquireControlLaw
  acquireGains acquireSensorModel acquireTestGeometry acquireErrorMetrics
  acquireCodeCustodian : ZhangDaibingReverseTarget

publishedControlLawImpliesSpecificDeployment : Bool
publishedControlLawImpliesSpecificDeployment = false

multiPaperSynthesisImpliesSingleSystem : Bool
multiPaperSynthesisImpliesSingleSystem = false

controlFamilyCanSupportBenignInspectionAutonomy : Bool
controlFamilyCanSupportBenignInspectionAutonomy = true
