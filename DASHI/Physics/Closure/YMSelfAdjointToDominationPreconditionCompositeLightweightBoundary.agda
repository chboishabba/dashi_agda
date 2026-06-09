module DASHI.Physics.Closure.YMSelfAdjointToDominationPreconditionCompositeLightweightBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

ym1Reference : String
ym1Reference =
  "DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessTheoremBoundary"

ym1ConsumerReference : String
ym1ConsumerReference =
  "DASHI.Physics.Closure.YMKillingBoundaryTheoremConsumerCompositeLightweightBoundary"

continuumRhoReference : String
continuumRhoReference =
  "DASHI.Physics.Closure.YMContinuumUniformRhoBoundBoundary"

continuumLeakageReference : String
continuumLeakageReference =
  "DASHI.Physics.Closure.YMContinuumUniformLeakageBoundBoundary"

data YMSelfAdjointToDominationClause : Set where
  finiteSelfAdjointQuotientInputRecorded : YMSelfAdjointToDominationClause
  quotientSymmetryFeedsClosableForm : YMSelfAdjointToDominationClause
  fullDegreeBoundaryConventionPreserved : YMSelfAdjointToDominationClause
  dominationPreconditionSocketRecorded : YMSelfAdjointToDominationClause
  continuumRhoBudgetAvailable : YMSelfAdjointToDominationClause
  continuumLeakageBudgetAvailable : YMSelfAdjointToDominationClause
  spectralMarginHandoffStillBlocked : YMSelfAdjointToDominationClause

canonicalYMSelfAdjointToDominationClauses :
  List YMSelfAdjointToDominationClause
canonicalYMSelfAdjointToDominationClauses =
  finiteSelfAdjointQuotientInputRecorded
  ∷ quotientSymmetryFeedsClosableForm
  ∷ fullDegreeBoundaryConventionPreserved
  ∷ dominationPreconditionSocketRecorded
  ∷ continuumRhoBudgetAvailable
  ∷ continuumLeakageBudgetAvailable
  ∷ spectralMarginHandoffStillBlocked
  ∷ []

ymSelfAdjointToDominationClauseCount : Nat
ymSelfAdjointToDominationClauseCount =
  listLength canonicalYMSelfAdjointToDominationClauses

ymSelfAdjointToDominationClauseCountIs7 :
  ymSelfAdjointToDominationClauseCount ≡ 7
ymSelfAdjointToDominationClauseCountIs7 = refl

data YMSelfAdjointToDominationBlocker : Set where
  blocker-ym1TheoremStillOpen : YMSelfAdjointToDominationBlocker
  blocker-finiteDominationStillOpen : YMSelfAdjointToDominationBlocker
  blocker-holonomyPositivePartStillOpen : YMSelfAdjointToDominationBlocker
  blocker-spectralMarginStillOpen : YMSelfAdjointToDominationBlocker
  blocker-ymClayPromotionForbidden : YMSelfAdjointToDominationBlocker

canonicalYMSelfAdjointToDominationBlockers :
  List YMSelfAdjointToDominationBlocker
canonicalYMSelfAdjointToDominationBlockers =
  blocker-ym1TheoremStillOpen
  ∷ blocker-finiteDominationStillOpen
  ∷ blocker-holonomyPositivePartStillOpen
  ∷ blocker-spectralMarginStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMSelfAdjointToDominationPreconditionCompositeRecorded : Bool
YMSelfAdjointToDominationPreconditionCompositeRecorded = true

YMSelfAdjointToDominationPreconditionCompositeProved : Bool
YMSelfAdjointToDominationPreconditionCompositeProved = false

record YMSelfAdjointToDominationPreconditionCompositeLightweightBoundary : Set where
  field
    clauses : List YMSelfAdjointToDominationClause
    clausesCanonical : clauses ≡ canonicalYMSelfAdjointToDominationClauses
    blockers : List YMSelfAdjointToDominationBlocker
    blockersCanonical : blockers ≡ canonicalYMSelfAdjointToDominationBlockers
    clauseCountIs7 : ymSelfAdjointToDominationClauseCount ≡ 7
    provedStillFalse :
      YMSelfAdjointToDominationPreconditionCompositeProved ≡ false

canonicalYMSelfAdjointToDominationPreconditionCompositeLightweightBoundary :
  YMSelfAdjointToDominationPreconditionCompositeLightweightBoundary
canonicalYMSelfAdjointToDominationPreconditionCompositeLightweightBoundary =
  record
    { clauses = canonicalYMSelfAdjointToDominationClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMSelfAdjointToDominationBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; provedStillFalse = refl
    }

YMSelfAdjointToDominationPreconditionCompositeRecordedIsTrue :
  YMSelfAdjointToDominationPreconditionCompositeRecorded ≡ true
YMSelfAdjointToDominationPreconditionCompositeRecordedIsTrue = refl
