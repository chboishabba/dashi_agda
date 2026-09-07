module DASHI.Core.ApplicationTransformationCapabilityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificCapabilityCarrierBidiExact as C

------------------------------------------------------------------------
-- APPLICATION TRANSFORMATION CAPABILITY, BIDI
--
-- Known physics/model knowledge is not identical to usable capability.  A
-- capability can live in the transformation from general law/model to a
-- validated, calibrated, configured, reproducible application.
------------------------------------------------------------------------

data TransformationCoordinate : Set where
  governingPhysics : TransformationCoordinate
  applicationGeometry : TransformationCoordinate
  constitutiveConfiguration : TransformationCoordinate
  calibrationState : TransformationCoordinate
  closureOrRegularisation : TransformationCoordinate
  sourceOrAlgorithmImplementation : TransformationCoordinate
  operatingWindow : TransformationCoordinate
  failureHistory : TransformationCoordinate
  qualificationEvidence : TransformationCoordinate
  validationCorpus : TransformationCoordinate
  uncertaintyModel : TransformationCoordinate
  integrationWorkflow : TransformationCoordinate
  tacitExecutionKnowledge : TransformationCoordinate


record ApplicationTransformation : Set where
  constructor application-transformation
  field
    domain : String
    publicFoundation : List TransformationCoordinate
    capabilityBearingTransformation : List TransformationCoordinate
    sourceReference : String
    boundedReading : String

open ApplicationTransformation public

record TransformationCapabilityReceipt : Set where
  constructor transformation-capability-receipt
  field
    transformation : ApplicationTransformation
    carrier : C.ScientificCapabilityCarrier
    reconstructive : C.ReconstructiveCarrierReceipt carrier
    sameApplicationObjectReference : String
    boundedClaim : String

open TransformationCapabilityReceipt public

data TransformationReverseTarget : Set where
  acquireApplicationGeometry : TransformationReverseTarget
  acquireCalibrationState : TransformationReverseTarget
  acquireConstitutiveConfiguration : TransformationReverseTarget
  acquireClosureOrRegularisation : TransformationReverseTarget
  acquireOperatingWindow : TransformationReverseTarget
  acquireFailureHistory : TransformationReverseTarget
  acquireQualificationEvidence : TransformationReverseTarget
  acquireValidationCorpus : TransformationReverseTarget
  acquireUncertaintyModel : TransformationReverseTarget
  acquireIntegrationWorkflow : TransformationReverseTarget
  acquireTacitExecutionKnowledge : TransformationReverseTarget
  acquirePersonRoleWeld : TransformationReverseTarget
  acquireSuccessorHandover : TransformationReverseTarget
  acquireObserverSurface : TransformationReverseTarget
  acquireEventLink : TransformationReverseTarget


record ApplicationTransformationBoundary : Set where
  constructor application-transformation-boundary
  field
    publicPhysicsImpliesPublicCapability : Bool
    publicPhysicsImpliesPublicCapabilityIsFalse : publicPhysicsImpliesPublicCapability ≡ false
    sameEquationsImpliesSameCapability : Bool
    sameEquationsImpliesSameCapabilityIsFalse : sameEquationsImpliesSameCapability ≡ false
    publishedArchitectureImpliesCalibratedApplication : Bool
    publishedArchitectureImpliesCalibratedApplicationIsFalse : publishedArchitectureImpliesCalibratedApplication ≡ false
    possessionOfTransformationImpliesUniqueHolder : Bool
    possessionOfTransformationImpliesUniqueHolderIsFalse : possessionOfTransformationImpliesUniqueHolder ≡ false
    transformationCriticalityImpliesTargeting : Bool
    transformationCriticalityImpliesTargetingIsFalse : transformationCriticalityImpliesTargeting ≡ false
    eventLinkRequiresIndependentEvidence : Bool
    eventLinkRequiresIndependentEvidenceIsTrue : eventLinkRequiresIndependentEvidence ≡ true

canonicalApplicationTransformationBoundary : ApplicationTransformationBoundary
canonicalApplicationTransformationBoundary = application-transformation-boundary false refl false refl false refl false refl false refl true refl
