module DASHI.ComputerScience.ChenShumingGraphHardwareVerificationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificCapabilityCarrierBidiExact as C
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T

------------------------------------------------------------------------
-- CHEN SHUMING: GRAPH-SPECIFICATION / SIMULATION HARDWARE VERIFICATION
--
-- Source anchor:
--   "Simulation-Based Hardware Verification with a Graph-Based Specification"
--   DOI 10.1155/2018/6398616.
--
-- This owner types the method's dataflow. It does not claim the publication is
-- the exact verification implementation used in any Galaxy/Feiteng processor.
------------------------------------------------------------------------

data VerificationStage : Set where
  graphSpecification stimulusConstruction simulationExecution
  observationExtraction specificationComparison residualClassification : VerificationStage

record GraphHardwareVerificationModel : Set where
  constructor graph-hardware-verification-model
  field
    sourceReference : String
    hardwareObject : String
    specificationObject : String
    stages : List VerificationStage
    verifiedClaim : String
    missingExecutableCoordinate : String

open GraphHardwareVerificationModel public

canonicalChenVerificationModel : GraphHardwareVerificationModel
canonicalChenVerificationModel = graph-hardware-verification-model
  "DOI 10.1155/2018/6398616"
  "digital hardware design under simulation"
  "graph-based hardware specification"
  (graphSpecification ∷ stimulusConstruction ∷ simulationExecution ∷
   observationExtraction ∷ specificationComparison ∷ residualClassification ∷ [])
  "simulation observations are compared against the graph-structured specification to expose verification residuals"
  "exact graph semantics, stimulus corpus, coverage metric, mismatch oracle and processor-specific instantiation"

chenVerificationCarrier : C.ScientificCapabilityCarrier
chenVerificationCarrier = C.scientific-capability-carrier
  "hardware verification"
  "graph-specification verification algorithm and validation corpus"
  C.sourceCodeOrAlgorithm
  C.carrierPublic
  "simulation-based verification against a graph-based specification"
  "DOI 10.1155/2018/6398616"
  "The published method is reconstructive at algorithm level; processor-specific specifications, stimuli and qualification evidence require separate receipts."

chenVerificationTransformation : T.ApplicationTransformation
chenVerificationTransformation = T.application-transformation
  "complex digital hardware verification"
  (T.sourceOrAlgorithmImplementation ∷ T.validationCorpus ∷ [])
  (T.failureHistory ∷ T.uncertaintyModel ∷ T.integrationWorkflow ∷ T.qualificationEvidence ∷ [])
  "DOI 10.1155/2018/6398616"
  "General method to validated processor verification requires target-specific graph semantics, tests, coverage and signoff evidence."

data ChenVerificationReverseTarget : Set where
  acquireGraphSemantics acquireStimulusCorpus acquireCoverageMetric
  acquireMismatchOracle acquireProcessorSameObjectReceipt acquireQualificationEvidence : ChenVerificationReverseTarget

chenVerificationReverseTargets : List ChenVerificationReverseTarget
chenVerificationReverseTargets =
  acquireGraphSemantics ∷ acquireStimulusCorpus ∷ acquireCoverageMetric ∷
  acquireMismatchOracle ∷ acquireProcessorSameObjectReceipt ∷ acquireQualificationEvidence ∷ []

publicationImpliesGalaxyProcessorInstantiation : Bool
publicationImpliesGalaxyProcessorInstantiation = false

methodIdentityImpliesDeploymentIdentity : Bool
methodIdentityImpliesDeploymentIdentity = false

hardwareVerificationCanRefineApplicationAcquisition : Bool
hardwareVerificationCanRefineApplicationAcquisition = true
