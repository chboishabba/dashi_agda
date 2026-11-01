module DASHI.Core.ScientificCapabilityCarrierBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificMechanismEvidenceBidiExact as S
import DASHI.Core.CriticalKnowledgeConcentrationBidiExact as K

------------------------------------------------------------------------
-- SCIENTIFIC CAPABILITY CARRIERS
--
-- Formalising a mechanism can reveal which technical objects actually carry
-- capability.  These are not person-attribution claims and do not imply
-- targeting, motive, disappearance causation, or homicide.
------------------------------------------------------------------------

data CapabilityCarrierKind : Set where
  governingModel : CapabilityCarrierKind
  constitutiveParameters : CapabilityCarrierKind
  sourceCodeOrAlgorithm : CapabilityCarrierKind
  calibrationData : CapabilityCarrierKind
  rawExperimentalData : CapabilityCarrierKind
  designGeometry : CapabilityCarrierKind
  processWindow : CapabilityCarrierKind
  fabricationRecipe : CapabilityCarrierKind
  qualificationEvidence : CapabilityCarrierKind
  failureModeMap : CapabilityCarrierKind
  integrationProcedure : CapabilityCarrierKind
  tacitTechnique : CapabilityCarrierKind
  hardwareConfiguration : CapabilityCarrierKind
  inverseModel : CapabilityCarrierKind


data CarrierEpistemicState : Set where
  carrierPublic : CarrierEpistemicState
  carrierBounded : CarrierEpistemicState
  carrierPartial : CarrierEpistemicState
  carrierUnknown : CarrierEpistemicState


record ScientificCapabilityCarrier : Set where
  constructor scientific-capability-carrier
  field
    scientificDomain : String
    carrierName : String
    kind : CapabilityCarrierKind
    state : CarrierEpistemicState
    mechanismReference : String
    sourceReference : String
    boundedReading : String

open ScientificCapabilityCarrier public

------------------------------------------------------------------------
-- Reconstructive carriers are those that can materially reduce the work needed
-- to reproduce, calibrate, qualify, diagnose, or extend a capability.
------------------------------------------------------------------------

data ReconstructiveRole : Set where
  descriptiveOnly : ReconstructiveRole
  reproducesModel : ReconstructiveRole
  reproducesExperiment : ReconstructiveRole
  reproducesProcess : ReconstructiveRole
  enablesCalibration : ReconstructiveRole
  enablesQualification : ReconstructiveRole
  enablesDiagnosis : ReconstructiveRole
  enablesExtension : ReconstructiveRole


record ReconstructiveCarrierReceipt (c : ScientificCapabilityCarrier) : Set where
  constructor reconstructive-carrier-receipt
  field
    role : ReconstructiveRole
    reconstructionReference : String
    boundedClaim : String

open ReconstructiveCarrierReceipt public

------------------------------------------------------------------------
-- Bridge into the existing critical-knowledge ontology.
-- This is proposition-relative: carrier kind suggests a possible coordinate,
-- but a person-specific knowledge receipt still needs independent evidence.
------------------------------------------------------------------------

carrierKindToKnowledgeCoordinate : CapabilityCarrierKind → K.KnowledgeCoordinate
carrierKindToKnowledgeCoordinate governingModel = K.publicKnowledge
carrierKindToKnowledgeCoordinate constitutiveParameters = K.configurationSpecificKnowledge
carrierKindToKnowledgeCoordinate sourceCodeOrAlgorithm = K.tacitImplementationKnowledge
carrierKindToKnowledgeCoordinate calibrationData = K.configurationSpecificKnowledge
carrierKindToKnowledgeCoordinate rawExperimentalData = K.sensitiveOrRestrictedKnowledge
carrierKindToKnowledgeCoordinate designGeometry = K.configurationSpecificKnowledge
carrierKindToKnowledgeCoordinate processWindow = K.configurationSpecificKnowledge
carrierKindToKnowledgeCoordinate fabricationRecipe = K.tacitImplementationKnowledge
carrierKindToKnowledgeCoordinate qualificationEvidence = K.failureModeKnowledge
carrierKindToKnowledgeCoordinate failureModeMap = K.failureModeKnowledge
carrierKindToKnowledgeCoordinate integrationProcedure = K.integrationKnowledge
carrierKindToKnowledgeCoordinate tacitTechnique = K.tacitImplementationKnowledge
carrierKindToKnowledgeCoordinate hardwareConfiguration = K.configurationSpecificKnowledge
carrierKindToKnowledgeCoordinate inverseModel = K.integrationKnowledge

record CarrierSupportsCriticalityHypothesis
    (c : ScientificCapabilityCarrier) : Set where
  constructor carrier-supports-criticality-hypothesis
  field
    reconstructiveReceipt : ReconstructiveCarrierReceipt c
    nonPublicOrPartial :
      (state c ≡ carrierBounded) ⊎
      (state c ≡ carrierPartial)
    supportReference : String

open CarrierSupportsCriticalityHypothesis public

------------------------------------------------------------------------
-- Reverse BIDI: once a carrier is identified, investigate its actual criticality
-- rather than promoting from technical interest alone.
------------------------------------------------------------------------

data ScientificCriticalityTarget : Set where
  carrierUniqueness : ScientificCriticalityTarget
  carrierNonPublicness : ScientificCriticalityTarget
  carrierIntegrationBreadth : ScientificCriticalityTarget
  carrierReplacementDifficulty : ScientificCriticalityTarget
  carrierStrategicRelevance : ScientificCriticalityTarget
  carrierObserverVisibility : ScientificCriticalityTarget
  personCarrierPossession : ScientificCriticalityTarget
  eventCausalLink : ScientificCriticalityTarget


record ScientificCriticalityReverseObligation : Set where
  constructor scientific-criticality-reverse-obligation
  field
    carrier : ScientificCapabilityCarrier
    target : ScientificCriticalityTarget
    requestedEvidence : String
    whatItCanPromote : String
    whatItCannotPromote : String

open ScientificCriticalityReverseObligation public

record ScientificCapabilityBoundary : Set where
  constructor scientific-capability-boundary
  field
    interestingScienceImpliesCriticalKnowledge : Bool
    interestingScienceImpliesCriticalKnowledgeIsFalse :
      interestingScienceImpliesCriticalKnowledge ≡ false
    reconstructiveCarrierImpliesUniqueHolder : Bool
    reconstructiveCarrierImpliesUniqueHolderIsFalse :
      reconstructiveCarrierImpliesUniqueHolder ≡ false
    boundedCarrierImpliesTargeting : Bool
    boundedCarrierImpliesTargetingIsFalse : boundedCarrierImpliesTargeting ≡ false
    targetingImpliesDisappearanceCause : Bool
    targetingImpliesDisappearanceCauseIsFalse :
      targetingImpliesDisappearanceCause ≡ false
    disappearanceImpliesHomicide : Bool
    disappearanceImpliesHomicideIsFalse : disappearanceImpliesHomicide ≡ false
    scientificFormalisationCanRefineAcquisitionTargets : Bool
    scientificFormalisationCanRefineAcquisitionTargetsIsTrue :
      scientificFormalisationCanRefineAcquisitionTargets ≡ true

canonicalScientificCapabilityBoundary : ScientificCapabilityBoundary
canonicalScientificCapabilityBoundary = scientific-capability-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
  true refl
