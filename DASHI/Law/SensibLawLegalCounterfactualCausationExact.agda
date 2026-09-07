module DASHI.Law.SensibLawLegalCounterfactualCausationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleCounterfactualWorldFamilyExact as Counterfactual

------------------------------------------------------------------------
-- SENSIBLAW LEGAL COUNTERFACTUAL CAUSATION
--
-- Domain-specific instantiation.  This file does not assert one jurisdiction's
-- causation doctrine.  A jurisdiction-specific source/authority owner must
-- supply the actual legal test.  The reusable discipline is:
--
--   admissible corrected legal world
--   -> outcome comparison
--   -> factual-causation identification state
--   -> separate scope / violation / liability / remedy / authority fibres.
------------------------------------------------------------------------

data LegalCorrection : Set where
  lawfulConductSubstitution : LegalCorrection
  omittedPrecautionSupplied : LegalCorrection
  prohibitedConductRemovedWithRelationRepaired : LegalCorrection
  institutionalDutyPerformed : LegalCorrection
  decisionProcedureCorrected : LegalCorrection
  unresolvedLegalCorrection : LegalCorrection


data LegalWorldAdmissibility : Set where
  legallyAdmissibleCounterfactual : LegalWorldAdmissibility
  legallyInadmissibleCounterfactual : LegalWorldAdmissibility
  legalAdmissibilityUnresolved : LegalWorldAdmissibility


data FactualCausationStatus : Set where
  factualCausationSatisfied : FactualCausationStatus
  factualCausationNotSatisfied : FactualCausationStatus
  factualCausationUnderidentified : FactualCausationStatus
  factualCausationUnresolved : FactualCausationStatus


data ScopeOfLiabilityStatus : Set where
  scopeSatisfied : ScopeOfLiabilityStatus
  scopeNotSatisfied : ScopeOfLiabilityStatus
  scopeUnderidentified : ScopeOfLiabilityStatus
  scopeUnresolved : ScopeOfLiabilityStatus


data LegalConsequenceStatus : Set where
  consequenceSatisfied : LegalConsequenceStatus
  consequenceNotSatisfied : LegalConsequenceStatus
  consequenceUnderidentified : LegalConsequenceStatus
  consequenceUnresolved : LegalConsequenceStatus


record LegalCounterfactualQuestion : Set₁ where
  constructor legal-counterfactual-question
  field
    World Outcome : Set
    observedWorld : World
    admissibleWorldFamily : Counterfactual.AdmissibleWorldFamily
    sameWorldCarrier : Counterfactual.World admissibleWorldFamily ≡ World
    legalCorrection : World → LegalCorrection
    legalAdmissibility : World → LegalWorldAdmissibility
    conductOrInstitutionalRelationReference : String
    harmedInterestReference : String
    wrongOrCauseOfActionReference : String
    jurisdictionReference : String
    legalSourceReference : String
    authorityReceiptReference : String
    questionReference : String

open LegalCounterfactualQuestion public

record CorrectedLegalWorld
    (question : LegalCounterfactualQuestion) : Set where
  constructor corrected-legal-world
  field
    world : World question
    correctionSpecified : legalCorrection question world ≡ unresolvedLegalCorrection → ⊥
    legalAdmissibilityExact : legalAdmissibility question world ≡ legallyAdmissibleCounterfactual
    notEventDeletionOnly : Set
    sameWrongOrCauseOfAction : Set
    sameHarmedInterestConsumer : Set
    jurisdictionHeldFixedOrJustified : Set
    legalSystemHeldFixedOrJustified : Set

open CorrectedLegalWorld public

------------------------------------------------------------------------
-- Identification may fail because multiple admissible corrected worlds remain.
------------------------------------------------------------------------

record LegalOutcomeDisagreement
    (question : LegalCounterfactualQuestion) : Set₁ where
  constructor legal-outcome-disagreement
  field
    left right : CorrectedLegalWorld question
    outcome : World question → Outcome question
    outcomesDiffer : outcome (world left) ≡ outcome (world right) → ⊥
    disagreementReference : String

open LegalOutcomeDisagreement public

underidentifiedWorldFamilyKeepsFactualCausationOpen :
  (question : LegalCounterfactualQuestion) →
  LegalOutcomeDisagreement question →
  FactualCausationStatus
underidentifiedWorldFamilyKeepsFactualCausationOpen question disagreement =
  factualCausationUnderidentified

------------------------------------------------------------------------
-- Separate downstream legal coordinates.
------------------------------------------------------------------------

record LegalCausationAssessment : Set where
  constructor legal-causation-assessment
  field
    factualCausation : FactualCausationStatus
    scopeOfLiability : ScopeOfLiabilityStatus
    violation : LegalConsequenceStatus
    liability : LegalConsequenceStatus
    remedy : LegalConsequenceStatus
    authority : LegalConsequenceStatus
    factualCausationProducerReference : String
    scopeProducerReference : String
    violationProducerReference : String
    liabilityProducerReference : String
    remedyProducerReference : String
    authorityProducerReference : String

open LegalCausationAssessment public

unresolvedAssessment : LegalCausationAssessment
unresolvedAssessment = legal-causation-assessment
  factualCausationUnresolved
  scopeUnresolved
  consequenceUnresolved
  consequenceUnresolved
  consequenceUnresolved
  consequenceUnresolved
  "factual-causation producer unresolved"
  "scope producer unresolved"
  "violation producer unresolved"
  "liability producer unresolved"
  "remedy producer unresolved"
  "authority producer unresolved"

------------------------------------------------------------------------
-- Explicit no-promotion laws.
------------------------------------------------------------------------

data FactualCausationImpliesScope : Set where
data FactualCausationImpliesViolation : Set where
data FactualCausationImpliesLiability : Set where
data FactualCausationImpliesRemedy : Set where
data FactualCausationImpliesAuthority : Set where
data CounterfactualAdmissibilityImpliesLegalLegitimacy : Set where
data EventDeletionEqualsCorrectedConduct : Set where
data OneAdmissibleWorldProvesUniqueCounterfactual : Set where

factualCausationDoesNotAutoPayScope : FactualCausationImpliesScope → ⊥
factualCausationDoesNotAutoPayScope ()

factualCausationDoesNotAutoPayViolation : FactualCausationImpliesViolation → ⊥
factualCausationDoesNotAutoPayViolation ()

factualCausationDoesNotAutoPayLiability : FactualCausationImpliesLiability → ⊥
factualCausationDoesNotAutoPayLiability ()

factualCausationDoesNotAutoPayRemedy : FactualCausationImpliesRemedy → ⊥
factualCausationDoesNotAutoPayRemedy ()

factualCausationDoesNotAutoPayAuthority : FactualCausationImpliesAuthority → ⊥
factualCausationDoesNotAutoPayAuthority ()

admissibleCounterfactualDoesNotProveLegitimacy :
  CounterfactualAdmissibilityImpliesLegalLegitimacy → ⊥
admissibleCounterfactualDoesNotProveLegitimacy ()

eventDeletionDoesNotSpecifyCorrectedConduct : EventDeletionEqualsCorrectedConduct → ⊥
eventDeletionDoesNotSpecifyCorrectedConduct ()

oneLocatedWorldDoesNotProveUniqueIdentification : OneAdmissibleWorldProvesUniqueCounterfactual → ⊥
oneLocatedWorldDoesNotProveUniqueIdentification ()

------------------------------------------------------------------------
-- Search/reopening surface for runtime consumers.
------------------------------------------------------------------------

data LegalCounterfactualResidual : Set where
  admissibilityResidual : LegalCounterfactualResidual
  correctedRelationResidual : LegalCounterfactualResidual
  heldFixedResidual : LegalCounterfactualResidual
  alternativeWorldResidual : LegalCounterfactualResidual
  outcomeComparisonResidual : LegalCounterfactualResidual
  causalIdentificationResidual : LegalCounterfactualResidual
  scopeResidual : LegalCounterfactualResidual
  liabilityResidual : LegalCounterfactualResidual
  remedyResidual : LegalCounterfactualResidual
  authorityResidual : LegalCounterfactualResidual
  closedForConsumer : LegalCounterfactualResidual


data CounterfactualProducer : Set where
  legalSourceProducer : CounterfactualProducer
  correctedConductProducer : CounterfactualProducer
  institutionalRelationProducer : CounterfactualProducer
  factualEvidenceProducer : CounterfactualProducer
  expertPhysicalModelProducer : CounterfactualProducer
  worldFamilyEnumerator : CounterfactualProducer
  comparisonProducer : CounterfactualProducer
  scopeProducer : CounterfactualProducer
  liabilityProducer : CounterfactualProducer
  remedyProducer : CounterfactualProducer
  authorityProducer : CounterfactualProducer
  noProducerRequired : CounterfactualProducer


producerForResidual : LegalCounterfactualResidual → CounterfactualProducer
producerForResidual admissibilityResidual = legalSourceProducer
producerForResidual correctedRelationResidual = correctedConductProducer
producerForResidual heldFixedResidual = factualEvidenceProducer
producerForResidual alternativeWorldResidual = worldFamilyEnumerator
producerForResidual outcomeComparisonResidual = comparisonProducer
producerForResidual causalIdentificationResidual = comparisonProducer
producerForResidual scopeResidual = scopeProducer
producerForResidual liabilityResidual = liabilityProducer
producerForResidual remedyResidual = remedyProducer
producerForResidual authorityResidual = authorityProducer
producerForResidual closedForConsumer = noProducerRequired

record SensibLawLegalCounterfactualBoundary : Set where
  constructor sensiblaw-legal-counterfactual-boundary
  field
    arbitraryAlternativeIsAdmissibleLegalWorld : Bool
    arbitraryAlternativeIsAdmissibleLegalWorldIsFalse :
      arbitraryAlternativeIsAdmissibleLegalWorld ≡ false
    deletingEventSpecifiesCorrectedRelation : Bool
    deletingEventSpecifiesCorrectedRelationIsFalse :
      deletingEventSpecifiesCorrectedRelation ≡ false
    multipleAdmissibleWorldsCanUnderidentifyCausation : Bool
    multipleAdmissibleWorldsCanUnderidentifyCausationIsTrue :
      multipleAdmissibleWorldsCanUnderidentifyCausation ≡ true
    factualCausationEqualsLiability : Bool
    factualCausationEqualsLiabilityIsFalse : factualCausationEqualsLiability ≡ false
    causalDependenceEqualsLegitimacy : Bool
    causalDependenceEqualsLegitimacyIsFalse : causalDependenceEqualsLegitimacy ≡ false
    consumerClosedMeansAllLegalAxesClosed : Bool
    consumerClosedMeansAllLegalAxesClosedIsFalse :
      consumerClosedMeansAllLegalAxesClosed ≡ false

canonicalSensibLawLegalCounterfactualBoundary : SensibLawLegalCounterfactualBoundary
canonicalSensibLawLegalCounterfactualBoundary =
  sensiblaw-legal-counterfactual-boundary
    false refl
    false refl
    true refl
    false refl
    false refl
    false refl
