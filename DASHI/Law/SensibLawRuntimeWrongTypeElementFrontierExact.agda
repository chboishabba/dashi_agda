module DASHI.Law.SensibLawRuntimeWrongTypeElementFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Law.SensibLawWrongTypeCausationElementExact as Element
import DASHI.Law.SensibLawProductionLegalRuntimeABIExact as Runtime

------------------------------------------------------------------------
-- RUNTIME WRONGTYPE ELEMENT FRONTIER
--
-- Turns the existing WrongType causation declarations/payments into an exact
-- consumer-facing frontier.  Critically, a generic element evaluation marked
-- `elementSatisfied` is not silently upgraded to a typed causation payment.
-- The payment constructors below require the exact payment objects already
-- owned by SensibLawWrongTypeCausationElementExact.
------------------------------------------------------------------------

data ElementEvaluationSurfaceStatus : Set where
  evaluationSatisfied : ElementEvaluationSurfaceStatus
  evaluationUnsatisfied : ElementEvaluationSurfaceStatus
  evaluationContested : ElementEvaluationSurfaceStatus
  evaluationUnresolved : ElementEvaluationSurfaceStatus


evaluationSurfaceStatus :
  Legal.ElementDisposition → ElementEvaluationSurfaceStatus
evaluationSurfaceStatus Legal.elementSatisfied = evaluationSatisfied
evaluationSurfaceStatus Legal.elementUnsatisfied = evaluationUnsatisfied
evaluationSurfaceStatus Legal.elementContested = evaluationContested
evaluationSurfaceStatus Legal.elementUnresolved = evaluationUnresolved

------------------------------------------------------------------------
-- Payment state is stronger than the generic evaluation surface.
------------------------------------------------------------------------

data CausationElementPaymentState
    {declaration : Element.WrongTypeCausationElementDeclaration}
    (weld : Element.ViolationWrongTypeCausationElementWeld declaration) : Set₁ where

  factualPaymentPaid :
    Element.FactualCausationElementPayment weld →
    CausationElementPaymentState weld

  scopePaymentPaid :
    Element.ScopeElementPayment weld →
    CausationElementPaymentState weld

  paymentMissing :
    Element.MissingCausationElementDemand declaration →
    CausationElementPaymentState weld

  paymentContested :
    Legal.disposition (Element.elementEvaluation weld) ≡ Legal.elementContested →
    CausationElementPaymentState weld

  paymentAuthorityBlocked :
    Set →
    CausationElementPaymentState weld

  paymentApplicabilityBlocked :
    Set →
    CausationElementPaymentState weld

  paymentInapplicable :
    Legal.resultingApplicability
      (Legal.applicabilityReceipt (Element.violation weld))
      ≡ Status.inapplicabilityAdmitted →
    CausationElementPaymentState weld

  paymentUnresolved :
    CausationElementPaymentState weld

------------------------------------------------------------------------
-- UI/runtime status projection.
------------------------------------------------------------------------

data LegalElementFrontierStatus : Set where
  paid : LegalElementFrontierStatus
  missing : LegalElementFrontierStatus
  contested : LegalElementFrontierStatus
  authorityBlocked : LegalElementFrontierStatus
  applicabilityBlocked : LegalElementFrontierStatus
  inapplicable : LegalElementFrontierStatus
  unresolved : LegalElementFrontierStatus


frontierStatus :
  {declaration : Element.WrongTypeCausationElementDeclaration} →
  {weld : Element.ViolationWrongTypeCausationElementWeld declaration} →
  CausationElementPaymentState weld →
  LegalElementFrontierStatus
frontierStatus (factualPaymentPaid _) = paid
frontierStatus (scopePaymentPaid _) = paid
frontierStatus (paymentMissing _) = missing
frontierStatus (paymentContested _) = contested
frontierStatus (paymentAuthorityBlocked _) = authorityBlocked
frontierStatus (paymentApplicabilityBlocked _) = applicabilityBlocked
frontierStatus (paymentInapplicable _) = inapplicable
frontierStatus paymentUnresolved = unresolved

------------------------------------------------------------------------
-- Producer routing remains typed and state-sensitive.
------------------------------------------------------------------------

data RuntimeLegalFrontierProducer : Set where
  noProducerRequired
  authorityProducerRequired
  applicabilityProducerRequired
  evidenceReviewProducerRequired
  causationProducerRequired :
    Element.CausationElementProducer → RuntimeLegalFrontierProducer

nextProducer :
  {declaration : Element.WrongTypeCausationElementDeclaration} →
  {weld : Element.ViolationWrongTypeCausationElementWeld declaration} →
  CausationElementPaymentState weld →
  RuntimeLegalFrontierProducer
nextProducer (factualPaymentPaid _) = noProducerRequired
nextProducer (scopePaymentPaid _) = noProducerRequired
nextProducer (paymentMissing demand) =
  causationProducerRequired (Element.requestedProducer demand)
nextProducer (paymentContested _) = evidenceReviewProducerRequired
nextProducer (paymentAuthorityBlocked _) = authorityProducerRequired
nextProducer (paymentApplicabilityBlocked _) = applicabilityProducerRequired
nextProducer (paymentInapplicable _) = noProducerRequired
nextProducer paymentUnresolved =
  causationProducerRequired Element.causationProducerUnresolved

------------------------------------------------------------------------
-- Exact runtime bundle.
------------------------------------------------------------------------

record RuntimeWrongTypeElementFrontier
    (meet : Runtime.RuntimeLegalTypedMeet)
    (declaration : Element.WrongTypeCausationElementDeclaration) : Set₁ where
  constructor runtimeWrongTypeElementFrontier
  field
    weld : Element.ViolationWrongTypeCausationElementWeld declaration
    sameRuntimeApplicabilityReceipt :
      Runtime.applicabilityReceipt meet
      ≡ Legal.applicabilityReceipt (Element.violation weld)

    evaluationStatus : ElementEvaluationSurfaceStatus
    evaluationStatusMatches :
      evaluationStatus
      ≡ evaluationSurfaceStatus (Legal.disposition (Element.elementEvaluation weld))

    paymentState : CausationElementPaymentState weld
    status : LegalElementFrontierStatus
    statusMatches : status ≡ frontierStatus paymentState

    producer : RuntimeLegalFrontierProducer
    producerMatches : producer ≡ nextProducer paymentState

    frontierReference : String

open RuntimeWrongTypeElementFrontier public

------------------------------------------------------------------------
-- Consumer-indexed closure: source/evaluation visibility is weaker than legal
-- element payment and final liability.
------------------------------------------------------------------------

data LegalConsumerGoal : Set where
  inspectSourceBackedElement : LegalConsumerGoal
  inspectElementEvaluation : LegalConsumerGoal
  establishTypedElementPayment : LegalConsumerGoal
  establishViolation : LegalConsumerGoal
  establishLiability : LegalConsumerGoal


data ConsumerGoalState : Set where goalOpen goalClosed goalBlocked : ConsumerGoalState

consumerGoalState :
  {declaration : Element.WrongTypeCausationElementDeclaration} →
  {weld : Element.ViolationWrongTypeCausationElementWeld declaration} →
  LegalConsumerGoal →
  CausationElementPaymentState weld →
  ConsumerGoalState
consumerGoalState inspectSourceBackedElement _ = goalClosed
consumerGoalState inspectElementEvaluation _ = goalClosed
consumerGoalState establishTypedElementPayment (factualPaymentPaid _) = goalClosed
consumerGoalState establishTypedElementPayment (scopePaymentPaid _) = goalClosed
consumerGoalState establishTypedElementPayment (paymentAuthorityBlocked _) = goalBlocked
consumerGoalState establishTypedElementPayment (paymentApplicabilityBlocked _) = goalBlocked
consumerGoalState establishTypedElementPayment (paymentInapplicable _) = goalBlocked
consumerGoalState establishTypedElementPayment _ = goalOpen
consumerGoalState establishViolation _ = goalOpen
consumerGoalState establishLiability _ = goalOpen

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data GenericSatisfiedEvaluationAutomaticallyTypedCausationPayment : Set where
data PaidCausationElementAutomaticallyViolation : Set where
data PaidCausationElementAutomaticallyLiability : Set where
data MissingElementAutomaticallySelectsEvidence : Set where
data SourceInspectionClosureMeansElementPayment : Set where

genericSatisfiedDoesNotAutoCreateTypedPayment :
  GenericSatisfiedEvaluationAutomaticallyTypedCausationPayment → ⊥
genericSatisfiedDoesNotAutoCreateTypedPayment ()

paidElementDoesNotAutoCreateViolation :
  PaidCausationElementAutomaticallyViolation → ⊥
paidElementDoesNotAutoCreateViolation ()

paidElementDoesNotAutoCreateLiability :
  PaidCausationElementAutomaticallyLiability → ⊥
paidElementDoesNotAutoCreateLiability ()

missingElementDoesNotAutoSelectEvidence :
  MissingElementAutomaticallySelectsEvidence → ⊥
missingElementDoesNotAutoSelectEvidence ()

sourceInspectionClosureDoesNotPayElement :
  SourceInspectionClosureMeansElementPayment → ⊥
sourceInspectionClosureDoesNotPayElement ()

record RuntimeWrongTypeElementBoundary : Set where
  constructor runtimeWrongTypeElementBoundary
  field
    genericEvaluationEqualsTypedPayment : Bool
    genericEvaluationEqualsTypedPaymentIsFalse :
      genericEvaluationEqualsTypedPayment ≡ false

    paymentEqualsViolation : Bool
    paymentEqualsViolationIsFalse : paymentEqualsViolation ≡ false

    paymentEqualsLiability : Bool
    paymentEqualsLiabilityIsFalse : paymentEqualsLiability ≡ false

    consumerClosureIsIndexed : Bool
    consumerClosureIsIndexedIsTrue : consumerClosureIsIndexed ≡ true

canonicalRuntimeWrongTypeElementBoundary : RuntimeWrongTypeElementBoundary
canonicalRuntimeWrongTypeElementBoundary =
  runtimeWrongTypeElementBoundary false refl false refl false refl true refl
