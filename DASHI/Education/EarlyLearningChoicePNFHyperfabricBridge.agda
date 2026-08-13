module DASHI.Education.EarlyLearningChoicePNFHyperfabricBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.EducationBodyMemoryBridge as EducationBody
import DASHI.Cognition.PNF.FibreLearningDynamics as FibreLearning
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge as TraumaMemory
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Education.RelationalEducationGateAlgebra as Education

------------------------------------------------------------------------
-- EARLY-LEARNING CHOICE / PNF / HYPERFABRIC BRIDGE
--
-- This module formalises a policy-architecture distinction, not an empirical
-- claim that one care route is always superior to another.
--
-- The central warning is that a public projection such as "families have more
-- choice" can identify situated family states whose developmental opportunity,
-- retained professional floor, safeguarding support, or learning support differ.
-- Intersectional non-factorability therefore applies before any reweighting of
-- the flattened choice variable is treated as an equity repair.
------------------------------------------------------------------------

data CareRoute : Set where
  professionalEarlyLearning familyCare familyDayCare outsideSchoolHoursCare : CareRoute

data FamilyPosition : Set where
  lowerSupportPosition higherSupportPosition : FamilyPosition

data PublicChoiceProjection : Set where
  universalChoiceMenu : PublicChoiceProjection

choiceProjection : FamilyPosition → PublicChoiceProjection
choiceProjection lowerSupportPosition = universalChoiceMenu
choiceProjection higherSupportPosition = universalChoiceMenu

------------------------------------------------------------------------
-- Finite structural witness: the same public menu need not determine the same
-- situated developmental opportunity.  The Bool values are a formal witness
-- only; they are not population estimates.
------------------------------------------------------------------------

developmentalOpportunityWitness : FamilyPosition → Bool
developmentalOpportunityWitness lowerSupportPosition = false
developmentalOpportunityWitness higherSupportPosition = true

situatedOpportunityDiffers :
  developmentalOpportunityWitness lowerSupportPosition ≡
  developmentalOpportunityWitness higherSupportPosition → ⊥
situatedOpportunityDiffers ()

uniformChoiceMenuNonFactorability :
  Intersection.NonFactorabilityWitness
    choiceProjection developmentalOpportunityWitness
uniformChoiceMenuNonFactorability =
  Intersection.nonFactorabilityWitness
    lowerSupportPosition
    higherSupportPosition
    refl
    situatedOpportunityDiffers

uniformChoiceCannotByItselfDetermineSituatedOpportunity :
  Intersection.FactorsThrough
    choiceProjection developmentalOpportunityWitness → ⊥
uniformChoiceCannotByItselfDetermineSituatedOpportunity =
  Intersection.witnessRulesOutEveryFlatFactorisation
    uniformChoiceMenuNonFactorability

------------------------------------------------------------------------
-- Addition versus substitution.
--
-- Two systems may both advertise "expanded choice" while only one retains the
-- professional early-learning floor.  Therefore expanded-choice branding is
-- not a sufficient carrier for whether professional capacity was preserved.
------------------------------------------------------------------------

data ChoiceCapacityState : Set where
  supportedAdditionalAlternative substitutionaryAlternative : ChoiceCapacityState

data ExpandedChoiceLabel : Set where
  expandedChoice : ExpandedChoiceLabel

expandedChoiceProjection : ChoiceCapacityState → ExpandedChoiceLabel
expandedChoiceProjection supportedAdditionalAlternative = expandedChoice
expandedChoiceProjection substitutionaryAlternative = expandedChoice

professionalFloorRetained : ChoiceCapacityState → Bool
professionalFloorRetained supportedAdditionalAlternative = true
professionalFloorRetained substitutionaryAlternative = false

professionalFloorDiffers :
  professionalFloorRetained supportedAdditionalAlternative ≡
  professionalFloorRetained substitutionaryAlternative → ⊥
professionalFloorDiffers ()

expandedChoiceDoesNotDetermineProfessionalFloor :
  Intersection.NonFactorabilityWitness
    expandedChoiceProjection professionalFloorRetained
expandedChoiceDoesNotDetermineProfessionalFloor =
  Intersection.nonFactorabilityWitness
    supportedAdditionalAlternative
    substitutionaryAlternative
    refl
    professionalFloorDiffers

expandedChoiceReweightingCannotRecoverMissingProfessionalFloor :
  Intersection.FactorsThrough
    expandedChoiceProjection professionalFloorRetained → ⊥
expandedChoiceReweightingCannotRecoverMissingProfessionalFloor =
  Intersection.witnessRulesOutEveryFlatFactorisation
    expandedChoiceDoesNotDetermineProfessionalFloor

------------------------------------------------------------------------
-- Policy hyperfabric.
--
-- A care route is not treated as one scalar.  Funding, workforce conditions,
-- learning-framework support, safeguarding, caregiver support and situated
-- equity remain separate fibres so that policy cannot silently trade one away
-- while preserving only the public "choice" label.
------------------------------------------------------------------------

record EarlyLearningPolicyHyperfabric : Set where
  constructor earlyLearningPolicyHyperfabric
  field
    route : CareRoute
    professionalFloorAvailable : Bool
    qualifiedEducatorCapacityFunded : Bool
    caregiverLabourRecognised : Bool
    learningFrameworkSupport : Bool
    childSafetySupport : Bool
    workingConditionsSupported : Bool
    situatedEquityAuditPresent : Bool
    routeIsAdditionalNotSubstitutionary : Bool
    policyReceipt : String

open EarlyLearningPolicyHyperfabric public

supportedFamilyAlternative : EarlyLearningPolicyHyperfabric
supportedFamilyAlternative =
  earlyLearningPolicyHyperfabric
    familyCare
    true
    true
    true
    true
    true
    true
    true
    true
    "family care is an additional supported route while the professional floor remains funded"

substitutionaryFamilyAlternative : EarlyLearningPolicyHyperfabric
substitutionaryFamilyAlternative =
  earlyLearningPolicyHyperfabric
    familyCare
    false
    false
    true
    false
    false
    false
    false
    false
    "family care is used as a substitute for professional early-learning capacity"

------------------------------------------------------------------------
-- Education gates remain typed requirements rather than being collapsed into
-- mere access.  This reuses the existing seven-gate education relation.
------------------------------------------------------------------------

record EarlyLearningEducationGateReceipt : Set where
  constructor earlyLearningEducationGateReceipt
  field
    voiceSupported : Bool
    agencySupported : Bool
    situatedEthicsSupported : Bool
    partnershipSupported : Bool
    enactmentSupported : Bool
    engagementIntelligenceSupported : Bool
    equityConditionsSupported : Bool
    gateGovernance : Education.EducationMetricGovernance
    accessAloneEqualsEquity : Bool
    accessAloneEqualsEquityIsFalse : accessAloneEqualsEquity ≡ false

canonicalEarlyLearningEducationGateReceipt : EarlyLearningEducationGateReceipt
canonicalEarlyLearningEducationGateReceipt =
  earlyLearningEducationGateReceipt
    true true true true true true true
    Education.canonicalEducationMetricGovernance
    false refl

------------------------------------------------------------------------
-- PNF learning / memory cross-pollination.
--
-- Revaluation, reinforcement, habituation, extinction and contextual learning
-- can alter salience, action weighting or transition topology while retaining
-- remembered semantic identity.  A sensory/context exposure (including an
-- olfactory exposure) is therefore represented as one possible context fibre,
-- not as proof of therapeutic effect or diagnosis.
------------------------------------------------------------------------

data LearningContextChannel : Set where
  relationalContext sensoryContext olfactoryContext spatialContext socialContext : LearningContextChannel

record ContextualFibreLearningReceipt : Set where
  constructor contextualFibreLearningReceipt
  field
    contextChannel : LearningContextChannel
    contextLabel : String
    learning : Learning.LearningReceipt
    fibreUpdate : FibreLearning.FibreLearningUpdate
    updateBeforeMatchesLearning :
      FibreLearning.before fibreUpdate ≡ Learning.before learning
    updateAfterMatchesLearning :
      FibreLearning.after fibreUpdate ≡ Learning.after learning
    rememberedSemanticIdentityPreserved :
      Memory.rememberedEvent (Learning.after learning) ≡
      Memory.rememberedEvent (Learning.before learning)
    contextExposureAloneProvesBenefit : Bool
    contextExposureAloneProvesBenefitIsFalse :
      contextExposureAloneProvesBenefit ≡ false
    contextExposureAloneProvesTrauma : Bool
    contextExposureAloneProvesTraumaIsFalse :
      contextExposureAloneProvesTrauma ≡ false

withinFibreContextUpdatePreservesRememberedPNF :
  (channel : LearningContextChannel) →
  (label : String) →
  (learning : Learning.LearningReceipt) →
  (update : FibreLearning.FibreLearningUpdate) →
  FibreLearning.before update ≡ Learning.before learning →
  FibreLearning.after update ≡ Learning.after learning →
  Memory.rememberedEvent (Learning.after learning) ≡
  Memory.rememberedEvent (Learning.before learning) →
  ContextualFibreLearningReceipt
withinFibreContextUpdatePreservesRememberedPNF
  channel label learning update beforeMatch afterMatch preserved =
  contextualFibreLearningReceipt
    channel label learning update beforeMatch afterMatch preserved
    false refl false refl

------------------------------------------------------------------------
-- Existing authority boundaries are reused, not weakened.
------------------------------------------------------------------------

record EarlyLearningPNFCrossPollination : Set where
  constructor earlyLearningPNFCrossPollination
  field
    educationBodyMemory : EducationBody.EducationBodyMemoryBridge
    traumaMemoryBoundary : TraumaMemory.TraumaMemoryHypervoxelAuthorityBoundary
    traumaMemoryBoundaryIsCanonical :
      traumaMemoryBoundary ≡
      TraumaMemory.canonicalTraumaMemoryHypervoxelAuthorityBoundary
    sameMenuImpliesSameSituatedOutcome : Bool
    sameMenuImpliesSameSituatedOutcomeIsFalse :
      sameMenuImpliesSameSituatedOutcome ≡ false
    paidFamilyCareEqualsProfessionalEducation : Bool
    paidFamilyCareEqualsProfessionalEducationIsFalse :
      paidFamilyCareEqualsProfessionalEducation ≡ false
    professionalEducationEqualsOnlyBabysitting : Bool
    professionalEducationEqualsOnlyBabysittingIsFalse :
      professionalEducationEqualsOnlyBabysitting ≡ false
    informalCareHasNoEducationalValue : Bool
    informalCareHasNoEducationalValueIsFalse :
      informalCareHasNoEducationalValue ≡ false
    familyChoiceAloneProvesEquity : Bool
    familyChoiceAloneProvesEquityIsFalse :
      familyChoiceAloneProvesEquity ≡ false
    sensoryExposureAloneProvesNeuroplasticBenefit : Bool
    sensoryExposureAloneProvesNeuroplasticBenefitIsFalse :
      sensoryExposureAloneProvesNeuroplasticBenefit ≡ false

------------------------------------------------------------------------
-- The canonical education/body-memory bridge is imported as a value rather
-- than duplicated.  Its exact constructor is intentionally left owned by the
-- Biology module; this bridge only requires the caller to supply that canonical
-- object when constructing the full cross-pollination receipt.
------------------------------------------------------------------------

mkCanonicalEarlyLearningPNFCrossPollination :
  (educationBridge : EducationBody.EducationBodyMemoryBridge) →
  EarlyLearningPNFCrossPollination
mkCanonicalEarlyLearningPNFCrossPollination educationBridge =
  earlyLearningPNFCrossPollination
    educationBridge
    TraumaMemory.canonicalTraumaMemoryHypervoxelAuthorityBoundary
    refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Compact statement of the integrated boundary.
------------------------------------------------------------------------

earlyLearningChoicePNFSummary : String
earlyLearningChoicePNFSummary =
  "family choice is one fibre, not the whole policy carrier: equal menus need not determine equal situated opportunity; additional family-care support is distinct from substitution away from professional capacity; PNF learning may reweight memory/action fibres without erasing semantic identity; intersectional, safeguarding, education-gate and trauma authority boundaries remain explicit."
