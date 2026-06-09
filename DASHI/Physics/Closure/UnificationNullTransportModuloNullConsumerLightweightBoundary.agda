module DASHI.Physics.Closure.UnificationNullTransportModuloNullConsumerLightweightBoundary where

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

nullStabilityReference : String
nullStabilityReference =
  "DASHI.Physics.Closure.UnificationNullClassStabilityLightweightBoundary"

moduloNullReference : String
moduloNullReference =
  "DASHI.Physics.Closure.UnificationModuloNullLinearityFromCrossTermNullityBoundary"

fourPointReference : String
fourPointReference =
  "DASHI.Physics.Closure.UnificationFourPointCancellationFromCrossTermNullityBoundary"

data NullTransportConsumerClause : Set where
  convertNullResidualToQuotientEquality :
    NullTransportConsumerClause
  substituteEquivalentRepresentativesInGluing :
    NullTransportConsumerClause
  proveModuloNullAdditivityOfGluing :
    NullTransportConsumerClause
  routeCrossTermNullityIntoFourPointInput :
    NullTransportConsumerClause
  exposeParallelogramConsumerWithoutPromoting :
    NullTransportConsumerClause

canonicalNullTransportConsumerClauses : List NullTransportConsumerClause
canonicalNullTransportConsumerClauses =
  convertNullResidualToQuotientEquality
  ∷ substituteEquivalentRepresentativesInGluing
  ∷ proveModuloNullAdditivityOfGluing
  ∷ routeCrossTermNullityIntoFourPointInput
  ∷ exposeParallelogramConsumerWithoutPromoting
  ∷ []

nullTransportConsumerClauseCount : Nat
nullTransportConsumerClauseCount =
  listLength canonicalNullTransportConsumerClauses

nullTransportConsumerClauseCountIs5 :
  nullTransportConsumerClauseCount ≡ 5
nullTransportConsumerClauseCountIs5 = refl

data NullTransportConsumerBlocker : Set where
  blocker-null-transport-theorem-unproved :
    NullTransportConsumerBlocker
  blocker-modulo-null-linearity-unproved :
    NullTransportConsumerBlocker
  blocker-four-point-unproved :
    NullTransportConsumerBlocker
  blocker-terminal-promotion-forbidden :
    NullTransportConsumerBlocker

canonicalNullTransportConsumerBlockers : List NullTransportConsumerBlocker
canonicalNullTransportConsumerBlockers =
  blocker-null-transport-theorem-unproved
  ∷ blocker-modulo-null-linearity-unproved
  ∷ blocker-four-point-unproved
  ∷ blocker-terminal-promotion-forbidden
  ∷ []

nullTransportConsumerBlockerCount : Nat
nullTransportConsumerBlockerCount =
  listLength canonicalNullTransportConsumerBlockers

nullTransportConsumerBlockerCountIs4 :
  nullTransportConsumerBlockerCount ≡ 4
nullTransportConsumerBlockerCountIs4 = refl

NullTransportModuloNullConsumerProvedLightweight : Bool
NullTransportModuloNullConsumerProvedLightweight = false

NullTransportModuloNullConsumerProvedLightweightIsFalse :
  NullTransportModuloNullConsumerProvedLightweight ≡ false
NullTransportModuloNullConsumerProvedLightweightIsFalse = refl

record UnificationNullTransportModuloNullConsumerLightweightBoundary : Set where
  field
    clauses : List NullTransportConsumerClause
    clausesAreCanonical : clauses ≡ canonicalNullTransportConsumerClauses
    blockers : List NullTransportConsumerBlocker
    blockersAreCanonical : blockers ≡ canonicalNullTransportConsumerBlockers
    clauseCountIs5 : nullTransportConsumerClauseCount ≡ 5
    blockerCountIs4 : nullTransportConsumerBlockerCount ≡ 4
    theoremStillFalse : NullTransportModuloNullConsumerProvedLightweight ≡ false

canonicalUnificationNullTransportModuloNullConsumerLightweightBoundary :
  UnificationNullTransportModuloNullConsumerLightweightBoundary
canonicalUnificationNullTransportModuloNullConsumerLightweightBoundary =
  record
    { clauses = canonicalNullTransportConsumerClauses
    ; clausesAreCanonical = refl
    ; blockers = canonicalNullTransportConsumerBlockers
    ; blockersAreCanonical = refl
    ; clauseCountIs5 = refl
    ; blockerCountIs4 = refl
    ; theoremStillFalse = refl
    }

UnificationNullTransportModuloNullConsumerLightweightBoundaryRecorded : Bool
UnificationNullTransportModuloNullConsumerLightweightBoundaryRecorded = true

UnificationNullTransportModuloNullConsumerLightweightBoundaryRecordedIsTrue :
  UnificationNullTransportModuloNullConsumerLightweightBoundaryRecorded ≡ true
UnificationNullTransportModuloNullConsumerLightweightBoundaryRecordedIsTrue = refl
