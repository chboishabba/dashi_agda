module DASHI.Cognition.PNF.SensibLawBrightonS185ViolationElementFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Law.SensibLawBrightonPremisesConditionEvidenceExact as Condition
import DASHI.Law.SensibLawBrightonMaintenanceChronologyEvidenceExact as Chronology

------------------------------------------------------------------------
-- BRIGHTON s 185: SHRUNK VIOLATION-ELEMENT FRONTIER
--
-- Paid factual coordinates:
--   1. material premises-condition / agent non-liveability recognition;
--   2. known remediation remained outstanding on 20 January 2023 after the
--      December quote/work-order process and required another urgent follow-up.
--
-- Still not paid:
--   whether that factual chronology establishes the exact statutory
--   maintenance-duty non-performance required for the selected s 185 violation
--   under the applicable historical source and legal-element compiler.
------------------------------------------------------------------------

conditionElementReference : String
conditionElementReference =
  "Brighton material premises-condition / agent non-liveability recognition"

outstandingRemediationElementReference : String
outstandingRemediationElementReference =
  "Brighton known remediation remained outstanding on 20 January 2023"

statutoryMaintenanceFailureElementReference : String
statutoryMaintenanceFailureElementReference =
  "Brighton exact s185 maintenance-duty non-performance at relevant time"

conditionElementEvaluation :
  (wrongTypeReference : Ontology.StableId) →
  Legal.WrongElementEvaluation
conditionElementEvaluation wrong =
  Legal.wrongElementEvaluation
    wrong
    conditionElementReference
    Legal.elementSatisfied
    []
    "paid narrowly by BrightonPremisesConditionEvidenceExact; private raw carriers excluded from public repo"

conditionElementDispositionIsSatisfied :
  ∀ wrong →
  Legal.disposition (conditionElementEvaluation wrong) ≡ Legal.elementSatisfied
conditionElementDispositionIsSatisfied wrong = refl

outstandingRemediationElementEvaluation :
  (wrongTypeReference : Ontology.StableId) →
  Legal.WrongElementEvaluation
outstandingRemediationElementEvaluation wrong =
  Legal.wrongElementEvaluation
    wrong
    outstandingRemediationElementReference
    Legal.elementSatisfied
    []
    "paid narrowly by BrightonMaintenanceChronologyEvidenceExact from the agent's 20 January delay/urgent-follow-up acknowledgement"

outstandingRemediationDispositionIsSatisfied :
  ∀ wrong →
  Legal.disposition (outstandingRemediationElementEvaluation wrong) ≡ Legal.elementSatisfied
outstandingRemediationDispositionIsSatisfied wrong = refl

firstOpenElementReference : String
firstOpenElementReference = statutoryMaintenanceFailureElementReference

firstOpenElementEvaluation :
  (wrongTypeReference : Ontology.StableId) →
  Legal.WrongElementEvaluation
firstOpenElementEvaluation wrong =
  Legal.wrongElementEvaluation
    wrong
    firstOpenElementReference
    Legal.elementUnresolved
    []
    "condition and outstanding-remediation facts are separately paid; exact historical-s185 legal evaluation remains open"

firstOpenElementDispositionIsUnresolved :
  ∀ wrong →
  Legal.disposition (firstOpenElementEvaluation wrong) ≡ Legal.elementUnresolved
firstOpenElementDispositionIsUnresolved wrong = refl

conditionBundlePaysNarrowCoordinate :
  Condition.narrowConditionCoordinatePaid
    Condition.canonicalBrightonPremisesConditionEvidenceBundle ≡ true
conditionBundlePaysNarrowCoordinate = refl

chronologyPaysOutstandingRemediationCoordinate :
  Chronology.narrowOutstandingRemediationCoordinatePaid
    Chronology.canonicalBrightonMaintenanceChronologyEvidence ≡ true
chronologyPaysOutstandingRemediationCoordinate = refl

chronologyDoesNotPayStatutoryS185Failure :
  Chronology.statutoryS185FailurePaid
    Chronology.canonicalBrightonMaintenanceChronologyEvidence ≡ false
chronologyDoesNotPayStatutoryS185Failure = refl

chronologyDoesNotPayWholeViolation :
  Chronology.wholeS185ViolationPaid
    Chronology.canonicalBrightonMaintenanceChronologyEvidence ≡ false
chronologyDoesNotPayWholeViolation = refl

data OutstandingRemediationAutomaticallyEqualsS185Failure : Set where
data NonLiveabilityNoticeAutomaticallyPaysMaintenanceFailure : Set where
data QSTARSAdvicePaysMaintenanceFailure : Set where
data RentOrderPaysS185MaintenanceFailure : Set where
data LaterExitCarrierAutomaticallyPaysJanuaryMaintenanceFailure : Set where
data SatisfiedFactsAutomaticallyCreateViolation : Set where

outstandingRemediationDoesNotAutoEqualS185Failure :
  OutstandingRemediationAutomaticallyEqualsS185Failure → ⊥
outstandingRemediationDoesNotAutoEqualS185Failure ()

nonLiveabilityNoticeDoesNotAutoPayMaintenanceFailure :
  NonLiveabilityNoticeAutomaticallyPaysMaintenanceFailure → ⊥
nonLiveabilityNoticeDoesNotAutoPayMaintenanceFailure ()

qstarsAdviceDoesNotPayMaintenanceFailure : QSTARSAdvicePaysMaintenanceFailure → ⊥
qstarsAdviceDoesNotPayMaintenanceFailure ()

rentOrderDoesNotPayS185MaintenanceFailure : RentOrderPaysS185MaintenanceFailure → ⊥
rentOrderDoesNotPayS185MaintenanceFailure ()

laterExitCarrierDoesNotAutoPayJanuaryMaintenanceFailure :
  LaterExitCarrierAutomaticallyPaysJanuaryMaintenanceFailure → ⊥
laterExitCarrierDoesNotAutoPayJanuaryMaintenanceFailure ()

satisfiedFactsDoNotAutoCreateViolation :
  SatisfiedFactsAutomaticallyCreateViolation → ⊥
satisfiedFactsDoNotAutoCreateViolation ()

record BrightonS185ViolationElementFrontierBoundary : Set where
  constructor brighton-s185-violation-element-frontier-boundary
  field
    conditionElementExplicit : Bool
    conditionElementSatisfied : Bool
    outstandingRemediationElementExplicit : Bool
    outstandingRemediationElementSatisfied : Bool
    statutoryMaintenanceFailureElementExplicit : Bool
    statutoryMaintenanceFailureDispositionUnresolved : Bool
    factualCoordinatesSeparatedFromLegalConclusion : Bool
    chronologyPaysOutstandingRemediation : Bool
    chronologyPaysStatutoryS185Failure : Bool
    chronologyPaysWholeViolation : Bool
    nonLiveabilityNoticeAutomaticallyPaysMaintenanceFailure : Bool
    qstarsAdvicePaysMaintenanceFailure : Bool
    rentOrderPaysMaintenanceFailure : Bool
    laterExitCarrierAutomaticallyPaysJanuaryMaintenanceFailure : Bool
    satisfiedFactsAutomaticallyCreateViolation : Bool

canonicalBrightonS185ViolationElementFrontierBoundary :
  BrightonS185ViolationElementFrontierBoundary
canonicalBrightonS185ViolationElementFrontierBoundary =
  brighton-s185-violation-element-frontier-boundary
    true true true true true true true true
    false false false false false false false
