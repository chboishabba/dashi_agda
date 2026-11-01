module DASHI.Physics.Closure.YMKillingBoundaryQuotientSymmetryLightweightBoundary where

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

descentReference : String
descentReference =
  "DASHI.Physics.Closure.YMKillingBoundaryGaugeQuotientDescentLightweightBoundary"

selfAdjointReference : String
selfAdjointReference =
  "DASHI.Physics.Closure.YMSelfAdjointFiniteHamiltonianBoundary"

data QuotientSymmetryClause : Set where
  defineQuotientBoundaryForm :
    QuotientSymmetryClause
  proveRepresentativesGiveSamePairing :
    QuotientSymmetryClause
  proveQuotientFormSymmetric :
    QuotientSymmetryClause
  proveHamiltonianGraphClosedOnQuotient :
    QuotientSymmetryClause
  showFiniteDeficiencyIndicesVanish :
    QuotientSymmetryClause
  identifyFiniteSelfAdjointOperator :
    QuotientSymmetryClause
  exposeDiscreteSpectrumConsumer :
    QuotientSymmetryClause

canonicalQuotientSymmetryClauses : List QuotientSymmetryClause
canonicalQuotientSymmetryClauses =
  defineQuotientBoundaryForm
  ∷ proveRepresentativesGiveSamePairing
  ∷ proveQuotientFormSymmetric
  ∷ proveHamiltonianGraphClosedOnQuotient
  ∷ showFiniteDeficiencyIndicesVanish
  ∷ identifyFiniteSelfAdjointOperator
  ∷ exposeDiscreteSpectrumConsumer
  ∷ []

quotientSymmetryClauseCount : Nat
quotientSymmetryClauseCount = listLength canonicalQuotientSymmetryClauses

quotientSymmetryClauseCountIs7 : quotientSymmetryClauseCount ≡ 7
quotientSymmetryClauseCountIs7 = refl

data QuotientSymmetryWitness : Set where
  quotientProjectionWitness :
    QuotientSymmetryWitness
  nullModeEliminationWitness :
    QuotientSymmetryWitness
  symmetricMatrixWitness :
    QuotientSymmetryWitness
  nonnegativeRayleighWitness :
    QuotientSymmetryWitness

canonicalQuotientSymmetryWitnesses : List QuotientSymmetryWitness
canonicalQuotientSymmetryWitnesses =
  quotientProjectionWitness
  ∷ nullModeEliminationWitness
  ∷ symmetricMatrixWitness
  ∷ nonnegativeRayleighWitness
  ∷ []

quotientSymmetryWitnessCount : Nat
quotientSymmetryWitnessCount = listLength canonicalQuotientSymmetryWitnesses

quotientSymmetryWitnessCountIs4 : quotientSymmetryWitnessCount ≡ 4
quotientSymmetryWitnessCountIs4 = refl

QuotientSymmetryTheoremProvedLightweight : Bool
QuotientSymmetryTheoremProvedLightweight = false

QuotientSymmetryTheoremProvedLightweightIsFalse :
  QuotientSymmetryTheoremProvedLightweight ≡ false
QuotientSymmetryTheoremProvedLightweightIsFalse = refl

record YMKillingBoundaryQuotientSymmetryLightweightBoundary : Set where
  field
    clauses : List QuotientSymmetryClause
    clausesAreCanonical : clauses ≡ canonicalQuotientSymmetryClauses
    witnesses : List QuotientSymmetryWitness
    witnessesAreCanonical : witnesses ≡ canonicalQuotientSymmetryWitnesses
    clauseCountIs7 : quotientSymmetryClauseCount ≡ 7
    witnessCountIs4 : quotientSymmetryWitnessCount ≡ 4
    theoremStillFalse : QuotientSymmetryTheoremProvedLightweight ≡ false

canonicalYMKillingBoundaryQuotientSymmetryLightweightBoundary :
  YMKillingBoundaryQuotientSymmetryLightweightBoundary
canonicalYMKillingBoundaryQuotientSymmetryLightweightBoundary =
  record
    { clauses = canonicalQuotientSymmetryClauses
    ; clausesAreCanonical = refl
    ; witnesses = canonicalQuotientSymmetryWitnesses
    ; witnessesAreCanonical = refl
    ; clauseCountIs7 = refl
    ; witnessCountIs4 = refl
    ; theoremStillFalse = refl
    }

YMQuotientSymmetryLightweightBoundaryRecorded : Bool
YMQuotientSymmetryLightweightBoundaryRecorded = true

YMQuotientSymmetryLightweightBoundaryRecordedIsTrue :
  YMQuotientSymmetryLightweightBoundaryRecorded ≡ true
YMQuotientSymmetryLightweightBoundaryRecordedIsTrue = refl
