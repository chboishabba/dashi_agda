{-# OPTIONS --safe #-}
module DASHI.Interop.IntrospectiveResidualNormalizationExact where

------------------------------------------------------------------------
-- NS R589/R592 LESSON, MADE REPOSITORY-WIDE
--
-- Two proof-search errors are distinct:
--
--   1. producer-tactic promotion: one successful route is mistaken for a
--      mandatory route to the consumer;
--   2. derived-intermediate inflation: a record/decomposition that can be
--      synthesized mechanically from smaller live payments is scheduled as a
--      primitive theorem obligation.
--
-- IntrospectiveProofLoopExact already blocks (1).  This owner blocks (2) and
-- gives theorem content priority over typecheck/submission/review metadata while
-- retaining all those statuses as real closure coordinates.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Interop.IntrospectiveProofLoopExact as Loop

record CompilerOwnedIntermediate
    (Primitive Intermediate ConsumerPayment : Set) : Set₁ where
  field
    compileIntermediate : Primitive → Intermediate
    primitivePayment : Primitive → ConsumerPayment
    intermediatePayment : Intermediate → ConsumerPayment
    paymentPreserved : ∀ primitive →
      intermediatePayment (compileIntermediate primitive)
      ≡ primitivePayment primitive

open CompilerOwnedIntermediate public

compilerOwnedIntermediateRole :
  ∀ {Primitive Intermediate ConsumerPayment} →
  CompilerOwnedIntermediate Primitive Intermediate ConsumerPayment →
  Loop.ProofSearchTargetRole
compilerOwnedIntermediateRole _ = Loop.compilerConsequence

data CompilerOwnedIntermediateCreatesPrimitiveDebtPermission : Set where

compilerOwnedIntermediateDoesNotCreatePrimitiveDebt :
  CompilerOwnedIntermediateCreatesPrimitiveDebtPermission → ⊥
compilerOwnedIntermediateDoesNotCreatePrimitiveDebt ()

------------------------------------------------------------------------
-- Closure sequencing.
--
-- "Closed" may legitimately have theorem, typecheck, submission, review and
-- acceptance coordinates.  But proof search should not spend theorem-search
-- cycles trying to improve later metadata while theorem content is still open.
------------------------------------------------------------------------

data ClosurePhase : Set where
  finishTheoremContent : ClosurePhase
  validateFormalArtifact : ClosurePhase
  pursueExternalClosure : ClosurePhase

nextClosurePhase : Loop.ClosureLedger → ClosurePhase
nextClosurePhase ledger with Loop.theoremContentClosed ledger
... | false = finishTheoremContent
... | true with Loop.typecheckedClosed ledger
... | false = validateFormalArtifact
... | true = pursueExternalClosure

openTheoremGetsPriority :
  ∀ {tc sub rev acc} →
  nextClosurePhase (Loop.closure-ledger false tc sub rev acc)
  ≡ finishTheoremContent
openTheoremGetsPriority = refl

typecheckedIsNextAfterTheorem :
  ∀ {sub rev acc} →
  nextClosurePhase (Loop.closure-ledger true false sub rev acc)
  ≡ validateFormalArtifact
typecheckedIsNextAfterTheorem = refl

externallyClosedPhaseAfterTheoremAndTypecheck :
  ∀ {sub rev acc} →
  nextClosurePhase (Loop.closure-ledger true true sub rev acc)
  ≡ pursueExternalClosure
externallyClosedPhaseAfterTheoremAndTypecheck = refl

record IntrospectiveResidualNormalizationBoundary : Set where
  constructor introspective-residual-normalization-boundary
  field
    compilerOwnedIntermediateIsPrimitiveResidual : Bool
    compilerOwnedIntermediateIsPrimitiveResidualIsFalse :
      compilerOwnedIntermediateIsPrimitiveResidual ≡ false

    preferredProducerTacticAutomaticallyMandatory : Bool
    preferredProducerTacticAutomaticallyMandatoryIsFalse :
      preferredProducerTacticAutomaticallyMandatory ≡ false

    theoremContentPrioritizedBeforeValidationMetadata : Bool
    theoremContentPrioritizedBeforeValidationMetadataIsTrue :
      theoremContentPrioritizedBeforeValidationMetadata ≡ true

    typecheckSubmissionReviewAcceptanceStillClosureCoordinates : Bool
    typecheckSubmissionReviewAcceptanceStillClosureCoordinatesIsTrue :
      typecheckSubmissionReviewAcceptanceStillClosureCoordinates ≡ true

canonicalIntrospectiveResidualNormalizationBoundary :
  IntrospectiveResidualNormalizationBoundary
canonicalIntrospectiveResidualNormalizationBoundary =
  introspective-residual-normalization-boundary
    false refl
    false refl
    true refl
    true refl
