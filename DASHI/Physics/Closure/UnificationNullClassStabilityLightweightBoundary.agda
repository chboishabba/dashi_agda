module DASHI.Physics.Closure.UnificationNullClassStabilityLightweightBoundary where

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

crossTermReference : String
crossTermReference =
  "DASHI.Physics.Closure.UnificationCrossTermNullityLightweightBoundary"

nullTransportReference : String
nullTransportReference =
  "DASHI.Physics.Closure.UnificationNullToQuotientEqualityTransportBoundary"

data NullClassStabilityClause : Set where
  chooseAdmissibleNullClass :
    NullClassStabilityClause
  defineRepresentativeChangeResidual :
    NullClassStabilityClause
  proveNullClassClosedUnderAddition :
    NullClassStabilityClause
  proveNullClassClosedUnderNegation :
    NullClassStabilityClause
  proveCrossTermResidualStableUnderRepresentativeChange :
    NullClassStabilityClause
  exposeTransportToQuotientEquality :
    NullClassStabilityClause

canonicalNullClassStabilityClauses : List NullClassStabilityClause
canonicalNullClassStabilityClauses =
  chooseAdmissibleNullClass
  ∷ defineRepresentativeChangeResidual
  ∷ proveNullClassClosedUnderAddition
  ∷ proveNullClassClosedUnderNegation
  ∷ proveCrossTermResidualStableUnderRepresentativeChange
  ∷ exposeTransportToQuotientEquality
  ∷ []

nullClassStabilityClauseCount : Nat
nullClassStabilityClauseCount = listLength canonicalNullClassStabilityClauses

nullClassStabilityClauseCountIs6 : nullClassStabilityClauseCount ≡ 6
nullClassStabilityClauseCountIs6 = refl

data NullClassStabilityWitness : Set where
  additiveClosureWitness :
    NullClassStabilityWitness
  negationClosureWitness :
    NullClassStabilityWitness
  representativeInvarianceWitness :
    NullClassStabilityWitness
  quotientTransportWitness :
    NullClassStabilityWitness

canonicalNullClassStabilityWitnesses : List NullClassStabilityWitness
canonicalNullClassStabilityWitnesses =
  additiveClosureWitness
  ∷ negationClosureWitness
  ∷ representativeInvarianceWitness
  ∷ quotientTransportWitness
  ∷ []

nullClassStabilityWitnessCount : Nat
nullClassStabilityWitnessCount = listLength canonicalNullClassStabilityWitnesses

nullClassStabilityWitnessCountIs4 : nullClassStabilityWitnessCount ≡ 4
nullClassStabilityWitnessCountIs4 = refl

NullClassStabilityTheoremProvedLightweight : Bool
NullClassStabilityTheoremProvedLightweight = false

NullClassStabilityTheoremProvedLightweightIsFalse :
  NullClassStabilityTheoremProvedLightweight ≡ false
NullClassStabilityTheoremProvedLightweightIsFalse = refl

record UnificationNullClassStabilityLightweightBoundary : Set where
  field
    clauses : List NullClassStabilityClause
    clausesAreCanonical : clauses ≡ canonicalNullClassStabilityClauses
    witnesses : List NullClassStabilityWitness
    witnessesAreCanonical : witnesses ≡ canonicalNullClassStabilityWitnesses
    clauseCountIs6 : nullClassStabilityClauseCount ≡ 6
    witnessCountIs4 : nullClassStabilityWitnessCount ≡ 4
    theoremStillFalse : NullClassStabilityTheoremProvedLightweight ≡ false

canonicalUnificationNullClassStabilityLightweightBoundary :
  UnificationNullClassStabilityLightweightBoundary
canonicalUnificationNullClassStabilityLightweightBoundary =
  record
    { clauses = canonicalNullClassStabilityClauses
    ; clausesAreCanonical = refl
    ; witnesses = canonicalNullClassStabilityWitnesses
    ; witnessesAreCanonical = refl
    ; clauseCountIs6 = refl
    ; witnessCountIs4 = refl
    ; theoremStillFalse = refl
    }

UnificationNullClassStabilityLightweightBoundaryRecorded : Bool
UnificationNullClassStabilityLightweightBoundaryRecorded = true

UnificationNullClassStabilityLightweightBoundaryRecordedIsTrue :
  UnificationNullClassStabilityLightweightBoundaryRecorded ≡ true
UnificationNullClassStabilityLightweightBoundaryRecordedIsTrue = refl
