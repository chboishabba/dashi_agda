module DASHI.Cognition.PNF.SensibLawBrightonS185ViolationElementFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Law.SensibLawBrightonPremisesConditionEvidenceExact as Condition

------------------------------------------------------------------------
-- BRIGHTON s 185: SPLIT VIOLATION-ELEMENT FRONTIER
--
-- The earlier frontier combined two different questions:
--   1. did a material premises-condition/non-liveability problem exist and was
--      it recognised by the managing agent by 24 January 2023?
--   2. did the lessor/agent fail the exact s 185 maintenance duty at the legally
--      relevant time, after accounting for repair chronology and other legal
--      conditions?
--
-- The reviewed private source corpus now pays (1) narrowly.  It does not pay
-- (2), and therefore does not itself pay the resulting s 185 violation.
------------------------------------------------------------------------

conditionElementReference : String
conditionElementReference =
  "Brighton material premises-condition / agent non-liveability recognition"

maintenanceFailureElementReference : String
maintenanceFailureElementReference =
  "Brighton s185 maintenance-duty non-performance at relevant time"

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

firstOpenElementReference : String
firstOpenElementReference = maintenanceFailureElementReference

firstOpenElementEvaluation :
  (wrongTypeReference : Ontology.StableId) →
  Legal.WrongElementEvaluation
firstOpenElementEvaluation wrong =
  Legal.wrongElementEvaluation
    wrong
    firstOpenElementReference
    Legal.elementUnresolved
    []
    "condition defect is separately paid; exact s185 non-performance still requires repair/remedy chronology and legal-element evaluation"

firstOpenElementDispositionIsUnresolved :
  ∀ wrong →
  Legal.disposition (firstOpenElementEvaluation wrong) ≡ Legal.elementUnresolved
firstOpenElementDispositionIsUnresolved wrong = refl

conditionBundlePaysNarrowCoordinate :
  Condition.narrowConditionCoordinatePaid
    Condition.canonicalBrightonPremisesConditionEvidenceBundle ≡ true
conditionBundlePaysNarrowCoordinate = refl

conditionBundleDoesNotPayMaintenanceFailure :
  Condition.statutoryMaintenanceFailurePaid
    Condition.canonicalBrightonPremisesConditionEvidenceBundle ≡ false
conditionBundleDoesNotPayMaintenanceFailure = refl

conditionBundleDoesNotPayViolation :
  Condition.section185ViolationPaid
    Condition.canonicalBrightonPremisesConditionEvidenceBundle ≡ false
conditionBundleDoesNotPayViolation = refl

data Form11AssertionAlonePaysMaintenanceFailure : Set where
data QSTARSAdvicePaysMaintenanceFailure : Set where
data NonLiveabilityNoticeAutomaticallyPaysMaintenanceFailure : Set where
data RentOrderPaysS185MaintenanceFailure : Set where
data LaterExitCarrierAutomaticallyPaysJanuaryMaintenanceFailure : Set where
data SatisfiedConditionElementAutomaticallyCreatesViolation : Set where

form11AssertionAloneDoesNotPayMaintenanceFailure :
  Form11AssertionAlonePaysMaintenanceFailure → ⊥
form11AssertionAloneDoesNotPayMaintenanceFailure ()

qstarsAdviceDoesNotPayMaintenanceFailure : QSTARSAdvicePaysMaintenanceFailure → ⊥
qstarsAdviceDoesNotPayMaintenanceFailure ()

nonLiveabilityNoticeDoesNotAutoPayMaintenanceFailure :
  NonLiveabilityNoticeAutomaticallyPaysMaintenanceFailure → ⊥
nonLiveabilityNoticeDoesNotAutoPayMaintenanceFailure ()

rentOrderDoesNotPayS185MaintenanceFailure : RentOrderPaysS185MaintenanceFailure → ⊥
rentOrderDoesNotPayS185MaintenanceFailure ()

laterExitCarrierDoesNotAutoPayJanuaryMaintenanceFailure :
  LaterExitCarrierAutomaticallyPaysJanuaryMaintenanceFailure → ⊥
laterExitCarrierDoesNotAutoPayJanuaryMaintenanceFailure ()

satisfiedConditionDoesNotAutoCreateViolation :
  SatisfiedConditionElementAutomaticallyCreatesViolation → ⊥
satisfiedConditionDoesNotAutoCreateViolation ()

record BrightonS185ViolationElementFrontierBoundary : Set where
  constructor brighton-s185-violation-element-frontier-boundary
  field
    conditionElementExplicit : Bool
    conditionElementSatisfied : Bool
    maintenanceFailureElementExplicit : Bool
    maintenanceFailureDispositionUnresolved : Bool
    conditionAndMaintenanceFailureSeparated : Bool
    requiresRepairChronologyForMaintenanceFailure : Bool
    conditionBundlePaysViolation : Bool
    nonLiveabilityNoticeAutomaticallyPaysMaintenanceFailure : Bool
    qstarsAdvicePaysMaintenanceFailure : Bool
    rentOrderPaysMaintenanceFailure : Bool
    laterExitCarrierAutomaticallyPaysJanuaryMaintenanceFailure : Bool
    conditionSatisfactionAutomaticallyCreatesViolation : Bool

canonicalBrightonS185ViolationElementFrontierBoundary :
  BrightonS185ViolationElementFrontierBoundary
canonicalBrightonS185ViolationElementFrontierBoundary =
  brighton-s185-violation-element-frontier-boundary
    true true true true true true
    false false false false false false
