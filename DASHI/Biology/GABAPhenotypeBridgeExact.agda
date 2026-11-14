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
-- Promotion receipts are evidence-indexed.  A validation source must be the
-- source carried by the exact evidence value being promoted.  Causal promotion
-- additionally carries a witness indexed by the exact association/estimand
-- pair, preventing a scope receipt for one association from being reused for a
-- different one merely because the outer types coincide.
------------------------------------------------------------------------

record PromotionValidation : Set where
  constructor promotion-validation
  field
    source : Source.AttributedSource
    validationReference : String
    validated : Bool
    validatedIsTrue : validated ≡ true

open PromotionValidation public

record AssociationEstimandScopeWitness
    (association : Evidence.RegionalGABAEvidence)
    (estimand : Causal.CausalEffectEstimand) : Set where
  constructor association-estimand-scope-witness
  field
    associationScopeReference : String
    estimandScopeReference : String
    populationAlignmentReference : String
    interventionComparatorReference : String
    outcomeTimeAlignmentReference : String

open AssociationEstimandScopeWitness public

record RegionalToWholeBrainBridge
    (regional : Evidence.RegionalGABAEvidence) : Set where
  constructor regional-to-whole-brain-bridge
  field
    validation : PromotionValidation
    validationSourceMatchesEvidence :
      source validation ≡ Evidence.source regional
    wholeBrainScopeReference : String
    transportReference : String

record GroupToIndividualBridge
    (groupEvidence : Evidence.RegionalGABAEvidence) : Set where
  constructor group-to-individual-bridge
  field
    validation : PromotionValidation
    validationSourceMatchesEvidence :
      source validation ≡ Evidence.source groupEvidence
    individualSelectionReference : String
    calibrationReference : String

record AssociationToCausalBridge
    (association : Evidence.RegionalGABAEvidence) : Set₂ where
  constructor association-to-causal-bridge
  field
    validation : PromotionValidation
    validationSourceMatchesEvidence :
      source validation ≡ Evidence.source association
    causalEstimand : Causal.CausalEffectEstimand
    estimandScopeMatchesAssociation :
      AssociationEstimandScopeWitness association causalEstimand
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
    validationSourceMatchesEvidence :
      source validation ≡ Evidence.source neurochemicalEvidence
    inflammatoryReadoutReference : String
    mediatorReference : String
    temporalDirectionReference : String

causalPromotionRequiresExistingEstimand :
  ∀ {association} →
  AssociationToCausalBridge association →
  Causal.CausalEffectEstimand
causalPromotionRequiresExistingEstimand bridge = causalEstimand bridge

causalPromotionRequiresMatchedScope :
  ∀ {association}
    (bridge : AssociationToCausalBridge association) →
  AssociationEstimandScopeWitness association (causalEstimand bridge)
causalPromotionRequiresMatchedScope bridge = estimandScopeMatchesAssociation bridge

------------------------------------------------------------------------
-- Evidence families.
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
    causalPromotionRequiresMatchedScope : Bool
    causalPromotionRequiresMatchedScopeIsTrue : causalPromotionRequiresMatchedScope ≡ true
    validationSourceMustMatchEvidence : Bool
    validationSourceMustMatchEvidenceIsTrue : validationSourceMustMatchEvidence ≡ true
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
    true refl
    true refl
