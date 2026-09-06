module DASHI.Culture.MissingDeceasedApplicationTransformationMatrixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T
import DASHI.Culture.MissingDeceasedScientificCapabilityCarrierMatrixExact as M

alloyTransformation : T.ApplicationTransformation
alloyTransformation = T.application-transformation
  "nickel-base burn-resistant superalloy"
  (T.governingPhysics ∷ [])
  (T.constitutiveConfiguration ∷ T.operatingWindow ∷ T.failureHistory ∷ T.qualificationEvidence ∷ T.integrationWorkflow ∷ T.tacitExecutionKnowledge ∷ [])
  "DASHI.Physics.Materials.NickelBaseSuperalloyProcessStateDepthExact"
  "Public composition and generic precipitation/oxidation science do not determine the validated heat-treatment, thermomechanical and microstructural process window."

fissionTransformation : T.ApplicationTransformation
fissionTransformation = T.application-transformation
  "space fission instrumentation and control"
  (T.governingPhysics ∷ [])
  (T.calibrationState ∷ T.operatingWindow ∷ T.failureHistory ∷ T.qualificationEvidence ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ T.integrationWorkflow ∷ [])
  "DASHI.Physics.Nuclear.FissionICQualificationReliabilityDepthExact"
  "Public I&C architecture and requirements do not determine component-specific drift, degradation, probability-of-failure and autonomous-recovery performance."

plasmaTransformation : T.ApplicationTransformation
plasmaTransformation = T.application-transformation
  "reduced fluid-kinetic plasma simulation"
  (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ [])
  (T.constitutiveConfiguration ∷ T.closureOrRegularisation ∷ T.operatingWindow ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ T.integrationWorkflow ∷ [])
  "DASHI.Physics.Plasma.ReducedKineticValidityClosureDepthExact"
  "Public equations and numerical architecture can still underdetermine application capability because ordering, closure, resolution, dissipation and target-specific validation matter."

radiographyTransformation : T.ApplicationTransformation
radiographyTransformation = T.application-transformation
  "flash radiography"
  (T.governingPhysics ∷ [])
  (T.applicationGeometry ∷ T.calibrationState ∷ T.closureOrRegularisation ∷ T.failureHistory ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ T.integrationWorkflow ∷ T.tacitExecutionKnowledge ∷ [])
  "DASHI.Physics.Accelerators.FlashRadiographyForwardInverseUncertaintyExact"
  "Public accelerator/radiography physics does not determine the calibrated source-object-detector forward model, inverse reconstruction, uncertainty and experiment-specific workflow."

spectroscopyTransformation : T.ApplicationTransformation
spectroscopyTransformation = T.application-transformation
  "cryogenic messenger-tag action spectroscopy"
  (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ [])
  (T.calibrationState ∷ T.constitutiveConfiguration ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ T.integrationWorkflow ∷ T.tacitExecutionKnowledge ∷ [])
  "DASHI.Chemistry.Spectroscopy.CryogenicTagPerturbationAndAssignmentDepthExact"
  "Public protocol and spectroscopy principles do not determine tag perturbation, conformer coverage, assignment uncertainty or mixture-specific discrimination performance."

radiographyTransformationReceipt : T.TransformationCapabilityReceipt
radiographyTransformationReceipt = T.transformation-capability-receipt radiographyTransformation M.radiographyInverseCarrier M.radiographyInverseReconstructive
  "same flash-radiography application carrier: calibrated source/object/detector inverse chain"
  "The reconstructive carrier is the application transformation, not the general accelerator or attenuation law."

alloyTransformationReceipt : T.TransformationCapabilityReceipt
alloyTransformationReceipt = T.transformation-capability-receipt alloyTransformation M.alloyProcessWindowCarrier M.alloyProcessWindowReconstructive
  "same superalloy application carrier: process-window/microstructure/property chain"
  "The reconstructive carrier is the validated process state, not nominal alloy chemistry alone."

fissionTransformationReceipt : T.TransformationCapabilityReceipt
fissionTransformationReceipt = T.transformation-capability-receipt fissionTransformation M.fissionQualificationCarrier M.fissionQualificationReconstructive
  "same space-fission application carrier: qualification/failure envelope"
  "The reconstructive carrier is the validated harsh-environment qualification state, not public block-level I&C architecture."

record CurrentApplicationTransformationAssessment : Set where
  constructor current-application-transformation-assessment
  field
    publicPhysicsCanUnderdetermineCapability : Bool
    publicPhysicsCanUnderdetermineCapabilityIsTrue : publicPhysicsCanUnderdetermineCapability ≡ true
    transformationCarriersIdentified : Bool
    transformationCarriersIdentifiedIsTrue : transformationCarriersIdentified ≡ true
    personSpecificPossessionClosed : Bool
    personSpecificPossessionClosedIsFalse : personSpecificPossessionClosed ≡ false
    eventCausalLinkClosed : Bool
    eventCausalLinkClosedIsFalse : eventCausalLinkClosed ≡ false

canonicalCurrentApplicationTransformationAssessment : CurrentApplicationTransformationAssessment
canonicalCurrentApplicationTransformationAssessment = current-application-transformation-assessment true refl true refl false refl false refl
