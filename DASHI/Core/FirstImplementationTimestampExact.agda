module DASHI.Core.FirstImplementationTimestampExact where

------------------------------------------------------------------------
-- TEMPORAL PROVENANCE / PRIORITY
--
-- Repository chronology is evidence about when an artefact existed in source.
-- It is not evidence that the artefact type-checked, was kernel-accepted, was
-- mathematically correct, was published, or had external priority.
--
-- The preferred repository-native first-implementation receipt is the earliest
-- recoverable Git commit containing the relevant implementation, together with
-- both UTC and explicitly-labelled local time.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

data ImplementationKind : Set where
  theoremStatementImplemented : ImplementationKind
  exactRepresentationImplemented : ImplementationKind
  compilerImplemented : ImplementationKind
  openConsumerImplemented : ImplementationKind
  candidateReceiptImplemented : ImplementationKind
  completedProofImplemented : ImplementationKind

data ValidationStage : Set where
  sourceCommittedOnly : ValidationStage
  typecheckObserved : ValidationStage
  exactHeadKernelObserved : ValidationStage

data ChronologyEvent : Set where
  firstImplementation : ChronologyEvent
  firstTypecheck : ChronologyEvent
  firstExactHeadKernelReceipt : ChronologyEvent
  firstPullRequest : ChronologyEvent
  firstMerge : ChronologyEvent
  firstPublication : ChronologyEvent
  externalRelease : ChronologyEvent

record FirstImplementationReceipt : Set where
  constructor first-implementation-receipt
  field
    artefact : String
    firstCommit : String
    firstImplementedUTC : String
    firstImplementedLocal : String
    localTimezone : String
    implementationKind : ImplementationKind
    validationAtFirstImplementation : ValidationStage

open FirstImplementationReceipt public

record LaterValidationReceipt : Set where
  constructor later-validation-receipt
  field
    validatedArtefact : String
    validationCommit : String
    validationTimeUTC : String
    validationTimeLocal : String
    validationTimezone : String
    validationStage : ValidationStage

open LaterValidationReceipt public

-- Empty permissions prevent chronology from being laundered into stronger
-- mathematical or validation claims.
data SourceCommitImpliesCorrectness : Set where
data SourceCommitImpliesKernelValidation : Set where
data TypecheckImpliesFirstImplementationDate : Set where
data LaterRefactorMayBackdateDifferentObject : Set where

sourceCommitDoesNotImplyCorrectness : SourceCommitImpliesCorrectness → ⊥
sourceCommitDoesNotImplyCorrectness ()

sourceCommitDoesNotImplyKernelValidation : SourceCommitImpliesKernelValidation → ⊥
sourceCommitDoesNotImplyKernelValidation ()

typecheckDoesNotDefineFirstImplementation : TypecheckImpliesFirstImplementationDate → ⊥
typecheckDoesNotDefineFirstImplementation ()

laterRefactorCannotBackdateDifferentObject : LaterRefactorMayBackdateDifferentObject → ⊥
laterRefactorCannotBackdateDifferentObject ()

firstImplementationChronologySeparatedFromValidation : Bool
firstImplementationChronologySeparatedFromValidation = true

firstImplementationChronologySeparatedFromValidationIsTrue :
  firstImplementationChronologySeparatedFromValidation ≡ true
firstImplementationChronologySeparatedFromValidationIsTrue = refl
