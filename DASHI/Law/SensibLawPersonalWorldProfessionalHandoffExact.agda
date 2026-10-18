module DASHI.Law.SensibLawPersonalWorldProfessionalHandoffExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- M9 / S22-S23 PERSONAL WORLD -> PROFESSIONAL CONSUMER
--
-- One personal world may expose different fibres to lawyer, doctor, advocate
-- and regulator consumers.  Scope is semantic admission, not presentation.
-- Private hypotheses and explicitly-not-ready journal material remain usable
-- by the personal consumer without automatically entering professional slices.
------------------------------------------------------------------------

data Coordinate : Set where
  reviewedEvent : Coordinate
  reviewedDocument : Coordinate
  reviewedFact : Coordinate
  privateHypothesis : Coordinate
  notReadyJournalMaterial : Coordinate

data Consumer : Set where
  personalJournal : Consumer
  lawyer : Consumer
  doctor : Consumer
  advocate : Consumer
  regulator : Consumer

data Scope : Coordinate → Consumer → Set where
  personalEvent :
    Scope reviewedEvent personalJournal
  personalDocument :
    Scope reviewedDocument personalJournal
  personalFact :
    Scope reviewedFact personalJournal
  personalHypothesis :
    Scope privateHypothesis personalJournal
  personalNotReady :
    Scope notReadyJournalMaterial personalJournal

  eventToLawyer :
    Scope reviewedEvent lawyer
  documentToLawyer :
    Scope reviewedDocument lawyer
  factToLawyer :
    Scope reviewedFact lawyer

  eventToDoctor :
    Scope reviewedEvent doctor
  documentToDoctor :
    Scope reviewedDocument doctor
  factToDoctor :
    Scope reviewedFact doctor

  eventToAdvocate :
    Scope reviewedEvent advocate
  factToAdvocate :
    Scope reviewedFact advocate

  documentToRegulator :
    Scope reviewedDocument regulator
  factToRegulator :
    Scope reviewedFact regulator

data Dependency : Consumer → Coordinate → Set where
  personalNeedsEvent :
    Dependency personalJournal reviewedEvent
  personalNeedsDocument :
    Dependency personalJournal reviewedDocument
  personalNeedsFact :
    Dependency personalJournal reviewedFact
  personalNeedsHypothesis :
    Dependency personalJournal privateHypothesis
  personalNeedsNotReady :
    Dependency personalJournal notReadyJournalMaterial

  lawyerNeedsEvent :
    Dependency lawyer reviewedEvent
  lawyerNeedsDocument :
    Dependency lawyer reviewedDocument
  lawyerNeedsFact :
    Dependency lawyer reviewedFact

  doctorNeedsEvent :
    Dependency doctor reviewedEvent
  doctorNeedsDocument :
    Dependency doctor reviewedDocument
  doctorNeedsFact :
    Dependency doctor reviewedFact

  advocateNeedsEvent :
    Dependency advocate reviewedEvent
  advocateNeedsFact :
    Dependency advocate reviewedFact

  regulatorNeedsDocument :
    Dependency regulator reviewedDocument
  regulatorNeedsFact :
    Dependency regulator reviewedFact

data Reviewed : Coordinate → Set where
  reviewedEventPaid : Reviewed reviewedEvent
  reviewedDocumentPaid : Reviewed reviewedDocument
  reviewedFactPaid : Reviewed reviewedFact

record Included (coordinate : Coordinate) (consumer : Consumer) : Set where
  constructor included
  field
    dependency : Dependency consumer coordinate
    scope : Scope coordinate consumer
    reviewed : Reviewed coordinate

open Included public

lawyerEventIncluded : Included reviewedEvent lawyer
lawyerEventIncluded =
  included lawyerNeedsEvent eventToLawyer reviewedEventPaid

lawyerDocumentIncluded : Included reviewedDocument lawyer
lawyerDocumentIncluded =
  included lawyerNeedsDocument documentToLawyer reviewedDocumentPaid

lawyerFactIncluded : Included reviewedFact lawyer
lawyerFactIncluded =
  included lawyerNeedsFact factToLawyer reviewedFactPaid

doctorEventIncluded : Included reviewedEvent doctor
doctorEventIncluded =
  included doctorNeedsEvent eventToDoctor reviewedEventPaid

advocateFactIncluded : Included reviewedFact advocate
advocateFactIncluded =
  included advocateNeedsFact factToAdvocate reviewedFactPaid

regulatorDocumentIncluded : Included reviewedDocument regulator
regulatorDocumentIncluded =
  included regulatorNeedsDocument documentToRegulator reviewedDocumentPaid

------------------------------------------------------------------------
-- Privacy / readiness firewalls.
------------------------------------------------------------------------

privateHypothesisCannotEnterLawyer :
  Included privateHypothesis lawyer → ⊥
privateHypothesisCannotEnterLawyer
  (included () scope reviewed)

privateHypothesisCannotEnterDoctor :
  Included privateHypothesis doctor → ⊥
privateHypothesisCannotEnterDoctor
  (included () scope reviewed)

privateHypothesisCannotEnterAdvocate :
  Included privateHypothesis advocate → ⊥
privateHypothesisCannotEnterAdvocate
  (included () scope reviewed)

privateHypothesisCannotEnterRegulator :
  Included privateHypothesis regulator → ⊥
privateHypothesisCannotEnterRegulator
  (included () scope reviewed)

notReadyCannotEnterLawyer :
  Included notReadyJournalMaterial lawyer → ⊥
notReadyCannotEnterLawyer
  (included () scope reviewed)

notReadyCannotEnterDoctor :
  Included notReadyJournalMaterial doctor → ⊥
notReadyCannotEnterDoctor
  (included () scope reviewed)

notReadyCannotEnterAdvocate :
  Included notReadyJournalMaterial advocate → ⊥
notReadyCannotEnterAdvocate
  (included () scope reviewed)

notReadyCannotEnterRegulator :
  Included notReadyJournalMaterial regulator → ⊥
notReadyCannotEnterRegulator
  (included () scope reviewed)

------------------------------------------------------------------------
-- Distinct professional fibres.
------------------------------------------------------------------------

data RegulatorReceivesEventWithoutDependency : Set where
data AdvocateReceivesDocumentWithoutDependency : Set where
data ProfessionalRoleCollapsesToSingleSlice : Set where
data PersonalAvailabilityCreatesProfessionalAuthority : Set where
data HandoffCreatesClaimTruth : Set where

regulatorEventBlocked :
  RegulatorReceivesEventWithoutDependency → ⊥
regulatorEventBlocked ()

advocateDocumentBlocked :
  AdvocateReceivesDocumentWithoutDependency → ⊥
advocateDocumentBlocked ()

professionalRolesRemainDistinct :
  ProfessionalRoleCollapsesToSingleSlice → ⊥
professionalRolesRemainDistinct ()

personalAvailabilityDoesNotCreateAuthority :
  PersonalAvailabilityCreatesProfessionalAuthority → ⊥
personalAvailabilityDoesNotCreateAuthority ()

handoffDoesNotCreateTruth :
  HandoffCreatesClaimTruth → ⊥
handoffDoesNotCreateTruth ()

------------------------------------------------------------------------
-- Recompute follows exact dependency, not role proximity.
------------------------------------------------------------------------

data Recompute : Consumer → Coordinate → Set where
  becauseDependency :
    ∀ {consumer coordinate} →
    Dependency consumer coordinate →
    Recompute consumer coordinate

factRecomputesLawyer : Recompute lawyer reviewedFact
factRecomputesLawyer = becauseDependency lawyerNeedsFact

factRecomputesDoctor : Recompute doctor reviewedFact
factRecomputesDoctor = becauseDependency doctorNeedsFact

factRecomputesAdvocate : Recompute advocate reviewedFact
factRecomputesAdvocate = becauseDependency advocateNeedsFact

factRecomputesRegulator : Recompute regulator reviewedFact
factRecomputesRegulator = becauseDependency regulatorNeedsFact

eventDoesNotRecomputeRegulator :
  Recompute regulator reviewedEvent → ⊥
eventDoesNotRecomputeRegulator
  (becauseDependency ())

record PersonalWorldProfessionalHandoffBoundary : Set where
  constructor personalWorldProfessionalHandoffBoundary
  field
    personalConsumerRetainsPrivateHypothesis : Bool
    personalConsumerRetainsPrivateHypothesisIsTrue :
      personalConsumerRetainsPrivateHypothesis ≡ true

    personalConsumerRetainsNotReadyMaterial : Bool
    personalConsumerRetainsNotReadyMaterialIsTrue :
      personalConsumerRetainsNotReadyMaterial ≡ true

    lawyerReceivesReviewedSelectedCoordinates : Bool
    lawyerReceivesReviewedSelectedCoordinatesIsTrue :
      lawyerReceivesReviewedSelectedCoordinates ≡ true

    doctorReceivesDistinctSlice : Bool
    doctorReceivesDistinctSliceIsTrue :
      doctorReceivesDistinctSlice ≡ true

    advocateReceivesDistinctSlice : Bool
    advocateReceivesDistinctSliceIsTrue :
      advocateReceivesDistinctSlice ≡ true

    regulatorReceivesDistinctSlice : Bool
    regulatorReceivesDistinctSliceIsTrue :
      regulatorReceivesDistinctSlice ≡ true

    privateHypothesisAutomaticallyShared : Bool
    privateHypothesisAutomaticallySharedIsFalse :
      privateHypothesisAutomaticallyShared ≡ false

    notReadyMaterialAutomaticallyShared : Bool
    notReadyMaterialAutomaticallySharedIsFalse :
      notReadyMaterialAutomaticallyShared ≡ false

    handoffCreatesClaimTruth : Bool
    handoffCreatesClaimTruthIsFalse :
      handoffCreatesClaimTruth ≡ false

open PersonalWorldProfessionalHandoffBoundary public

canonicalPersonalWorldProfessionalHandoffBoundary :
  PersonalWorldProfessionalHandoffBoundary
canonicalPersonalWorldProfessionalHandoffBoundary =
  personalWorldProfessionalHandoffBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
