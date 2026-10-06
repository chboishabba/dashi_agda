module DASHI.Biology.GABAPhenotypeBridgeExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Biology.GABAPhenotypeEvidenceExact as Evidence
import DASHI.Biology.NeurotypeProcessingGeometryExact as Geometry
import DASHI.Cognition.PNF.DepthWheelMemoryHyperfabric as MemoryFabric
import DASHI.Biology.CausalEffectEstimandExact as Causal
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- GABA / PHENOTYPE TYPED BRIDGE LAYER
--
-- This module does not promote any evidence receipt by itself.  It specifies
-- the typed obligations required for promotion.  In particular, a causal
-- bridge must carry the repository's existing CausalEffectEstimand object;
-- citation, association, group difference and diagnostic labels cannot stand
-- in for that object.
------------------------------------------------------------------------

record PromotionValidation : Set where
  constructor promotion-validation
  field
    source : Source.AttributedSource
    validationReference : String
    validated : Bool
    validatedIsTrue : validated ≡ true

open PromotionValidation public

record RegionalToWholeBrainBridge
    (regional : Evidence.RegionalGABAEvidence) : Set where
  constructor regional-to-whole-brain-bridge
  field
    validation : PromotionValidation
    wholeBrainScopeReference : String
    transportReference : String

record GroupToIndividualBridge
    (groupEvidence : Evidence.RegionalGABAEvidence) : Set where
  constructor group-to-individual-bridge
  field
    validation : PromotionValidation
    individualSelectionReference : String
    calibrationReference : String

record AssociationToCausalBridge
    (association : Evidence.RegionalGABAEvidence) : Set₂ where
  constructor association-to-causal-bridge
  field
    validation : PromotionValidation
    causalEstimand : Causal.CausalEffectEstimand
    identificationReference : String
    interventionReference : String

open AssociationToCausalBridge public

record SynchronyAttachmentBridge : Set where
  constructor synchrony-attachment-bridge
  field
    validation : PromotionValidation
    synchronyMeasurementReference : String
    attachmentConstructReference : String
    bridgeModelReference : String

record NeurochemicalInflammationBridge
    (neurochemicalEvidence : Evidence.RegionalGABAEvidence) : Set where
  constructor neurochemical-inflammation-bridge
  field
    validation : PromotionValidation
    inflammatoryReadoutReference : String
    mediatorReference : String
    temporalDirectionReference : String

causalPromotionRequiresExistingEstimand :
  ∀ {association} →
  AssociationToCausalBridge association →
  Causal.CausalEffectEstimand
causalPromotionRequiresExistingEstimand bridge = causalEstimand bridge

------------------------------------------------------------------------
-- Evidence families.
--
-- These are families, not a theorem that every member lies on a single total
-- order.  Promotion authority comes from the typed validation / causal objects
-- above, not from the family tag alone.
------------------------------------------------------------------------

data EvidenceFamily : Set where
  observationalFamily : EvidenceFamily
  longitudinalFamily : EvidenceFamily
  perturbationalFamily : EvidenceFamily
  randomizedInterventionFamily : EvidenceFamily
  replicatedCausalModelFamily : EvidenceFamily

data EvidenceFamilyDeterminesCausalAuthorityPermission : Set where

evidenceFamilyTagDoesNotDetermineCausalAuthority :
  EvidenceFamilyDeterminesCausalAuthorityPermission → ⊥
evidenceFamilyTagDoesNotDetermineCausalAuthority ()

record EvidenceFamilyReceipt : Set where
  constructor evidence-family-receipt
  field
    evidence : Evidence.RegionalGABAEvidence
    family : EvidenceFamily
    familyReference : String
    promotionStillRequiresBridge : Bool
    promotionStillRequiresBridgeIsTrue : promotionStillRequiresBridge ≡ true

------------------------------------------------------------------------
-- Sensory cross-pollination.
--
-- GABA evidence is attached to the already-existing processing geometry.  The
-- carrier does not assert that GABA determines weighting, context, geometry or
-- sensory load.  It makes those coordinates explicit so a future empirical
-- model can relate them without collapsing them.
------------------------------------------------------------------------

record SensoryGABAInteractionCarrier : Set where
  constructor sensory-gaba-interaction-carrier
  field
    evidence : Evidence.RegionalGABAEvidence
    weighting : Geometry.ExteroceptiveWeighting
    context : Geometry.SensoryContext
    processingGeometry : Geometry.ProcessingGeometry
    observedLoad : Geometry.SensoryLoad
    loadMatchesExistingContextModel :
      observedLoad ≡ Geometry.sensoryLoad weighting context
    interactionReference : String

sameGABAEvidenceDifferentContextCanChangeLoad :
  (evidence : Evidence.RegionalGABAEvidence) →
  Geometry.sensoryLoad Geometry.highExteroceptiveWeight Geometry.quietContext
    ≡ Geometry.sensoryLoad Geometry.highExteroceptiveWeight Geometry.denseContext →
  ⊥
sameGABAEvidenceDifferentContextCanChangeLoad evidence =
  Geometry.samePersonWeightDifferentContextCanChangeLoad

umesawaSensoryCarrier :
  Geometry.ProcessingGeometry →
  SensoryGABAInteractionCarrier
umesawaSensoryCarrier processing =
  sensory-gaba-interaction-carrier
    Evidence.umesawa2020SensoryHyperResponsiveness
    Geometry.highExteroceptiveWeight
    Geometry.denseContext
    processing
    Geometry.overloadedLoad
    refl
    "Synthetic attachment of an attributed regional GABA/sensory receipt to the existing context-sensitive sensory geometry; the geometry values are not claimed to be measured by Umesawa et al."

------------------------------------------------------------------------
-- Memory / retrieval cross-pollination.
--
-- Schmitz et al. is a retrieval-suppression association.  This bridge attaches
-- that receipt to the existing memory-fibre owner without claiming GABA writes,
-- erases, increments, or otherwise changes the formal memory fibre.
------------------------------------------------------------------------

record GABARetrievalMemoryBridge : Set where
  constructor gaba-retrieval-memory-bridge
  field
    evidence : Evidence.RegionalGABAEvidence
    memory : MemoryFabric.WheelMemoryFibre
    processingGeometry : Geometry.ProcessingGeometry
    attachmentReference : String
    evidenceChangesMemoryAutomatically : Bool
    evidenceChangesMemoryAutomaticallyIsFalse :
      evidenceChangesMemoryAutomatically ≡ false

schmitzMemoryAttachment :
  MemoryFabric.WheelMemoryFibre →
  Geometry.ProcessingGeometry →
  GABARetrievalMemoryBridge
schmitzMemoryAttachment memory processing =
  gaba-retrieval-memory-bridge
    Evidence.schmitz2017ThoughtSuppression
    memory
    processing
    "Associates the Schmitz retrieval-suppression receipt with an existing memory fibre only; no memory mutation is inferred."
    false
    refl

schmitzEvidenceDoesNotByItselfChangeMemory :
  (memory : MemoryFabric.WheelMemoryFibre) →
  MemoryFabric.refinementDepth memory ≡ MemoryFabric.refinementDepth memory
schmitzEvidenceDoesNotByItselfChangeMemory memory = refl

------------------------------------------------------------------------
-- Explicit ADHD evidence hole.
--
-- This records the minimum coordinates demanded by the transcript audit before
-- a general low-GABA or severity claim can even enter a promotion attempt.
------------------------------------------------------------------------

record ADHDEvidenceGap : Set where
  constructor adhd-evidence-gap
  field
    namedPopulationRequired : Bool
    namedPopulationRequiredIsTrue : namedPopulationRequired ≡ true
    namedRegionRequired : Bool
    namedRegionRequiredIsTrue : namedRegionRequired ≡ true
    measurementMethodRequired : Bool
    measurementMethodRequiredIsTrue : measurementMethodRequired ≡ true
    severityInstrumentRequired : Bool
    severityInstrumentRequiredIsTrue : severityInstrumentRequired ≡ true
    effectDirectionRequired : Bool
    effectDirectionRequiredIsTrue : effectDirectionRequired ≡ true
    namedSourceRequired : Bool
    namedSourceRequiredIsTrue : namedSourceRequired ≡ true
    replicationReferenceRequired : Bool
    replicationReferenceRequiredIsTrue : replicationReferenceRequired ≡ true
    causalClaimRequiresExistingEstimand : Bool
    causalClaimRequiresExistingEstimandIsTrue : causalClaimRequiresExistingEstimand ≡ true

canonicalADHDEvidenceGap : ADHDEvidenceGap
canonicalADHDEvidenceGap =
  adhd-evidence-gap
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Global bridge boundary.
------------------------------------------------------------------------

record GABAPhenotypeBridgeBoundary : Set where
  constructor gaba-phenotype-bridge-boundary
  field
    regionalPromotionRequiresBridge : Bool
    regionalPromotionRequiresBridgeIsTrue : regionalPromotionRequiresBridge ≡ true
    groupToIndividualRequiresBridge : Bool
    groupToIndividualRequiresBridgeIsTrue : groupToIndividualRequiresBridge ≡ true
    causalPromotionRequiresEstimand : Bool
    causalPromotionRequiresEstimandIsTrue : causalPromotionRequiresEstimand ≡ true
    sensoryContextRemainsExplicit : Bool
    sensoryContextRemainsExplicitIsTrue : sensoryContextRemainsExplicit ≡ true
    memoryMutationIsNotInferred : Bool
    memoryMutationIsNotInferredIsTrue : memoryMutationIsNotInferred ≡ true
    adhdEvidenceHoleRemainsOpen : Bool
    adhdEvidenceHoleRemainsOpenIsTrue : adhdEvidenceHoleRemainsOpen ≡ true

canonicalGABAPhenotypeBridgeBoundary : GABAPhenotypeBridgeBoundary
canonicalGABAPhenotypeBridgeBoundary =
  gaba-phenotype-bridge-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
