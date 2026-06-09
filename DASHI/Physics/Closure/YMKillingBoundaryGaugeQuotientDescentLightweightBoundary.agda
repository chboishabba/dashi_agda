module DASHI.Physics.Closure.YMKillingBoundaryGaugeQuotientDescentLightweightBoundary where

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

gaugeDomainReference : String
gaugeDomainReference =
  "DASHI.Physics.Closure.YMKillingBoundaryGaugeDomainPreservationBoundary"

quotientCarrierReference : String
quotientCarrierReference =
  "DASHI.Physics.Closure.YMFiniteGaugeQuotientCarrierConstructionBoundary"

data GaugeQuotientDescentClause : Set where
  defineFiniteGaugeOrbitRelation :
    GaugeQuotientDescentClause
  defineBoundaryGaugeNullSubspace :
    GaugeQuotientDescentClause
  proveBoundaryFormKillsGaugeNullModes :
    GaugeQuotientDescentClause
  proveHamiltonianPreservesGaugeDomain :
    GaugeQuotientDescentClause
  descendBoundaryPairingToQuotient :
    GaugeQuotientDescentClause
  descendHamiltonianToQuotient :
    GaugeQuotientDescentClause
  preserveSymmetricFormAfterQuotient :
    GaugeQuotientDescentClause
  handoffToFiniteSelfAdjointOperator :
    GaugeQuotientDescentClause

canonicalGaugeQuotientDescentClauses : List GaugeQuotientDescentClause
canonicalGaugeQuotientDescentClauses =
  defineFiniteGaugeOrbitRelation
  ∷ defineBoundaryGaugeNullSubspace
  ∷ proveBoundaryFormKillsGaugeNullModes
  ∷ proveHamiltonianPreservesGaugeDomain
  ∷ descendBoundaryPairingToQuotient
  ∷ descendHamiltonianToQuotient
  ∷ preserveSymmetricFormAfterQuotient
  ∷ handoffToFiniteSelfAdjointOperator
  ∷ []

gaugeQuotientDescentClauseCount : Nat
gaugeQuotientDescentClauseCount =
  listLength canonicalGaugeQuotientDescentClauses

gaugeQuotientDescentClauseCountIs8 :
  gaugeQuotientDescentClauseCount ≡ 8
gaugeQuotientDescentClauseCountIs8 = refl

data GaugeQuotientInvariant : Set where
  quotientProjectionIdempotent :
    GaugeQuotientInvariant
  constantGaugeModeRemoved :
    GaugeQuotientInvariant
  descendedFormRepresentativeIndependent :
    GaugeQuotientInvariant
  quotientHamiltonianSymmetryVisible :
    GaugeQuotientInvariant

canonicalGaugeQuotientInvariants : List GaugeQuotientInvariant
canonicalGaugeQuotientInvariants =
  quotientProjectionIdempotent
  ∷ constantGaugeModeRemoved
  ∷ descendedFormRepresentativeIndependent
  ∷ quotientHamiltonianSymmetryVisible
  ∷ []

gaugeQuotientInvariantCount : Nat
gaugeQuotientInvariantCount = listLength canonicalGaugeQuotientInvariants

gaugeQuotientInvariantCountIs4 : gaugeQuotientInvariantCount ≡ 4
gaugeQuotientInvariantCountIs4 = refl

data GaugeQuotientDescentBlocker : Set where
  blocker-gauge-domain-descent-unproved :
    GaugeQuotientDescentBlocker
  blocker-quotient-symmetry-unproved :
    GaugeQuotientDescentBlocker
  blocker-self-adjointness-unproved :
    GaugeQuotientDescentBlocker
  blocker-ym-clay-forbidden :
    GaugeQuotientDescentBlocker

canonicalGaugeQuotientDescentBlockers :
  List GaugeQuotientDescentBlocker
canonicalGaugeQuotientDescentBlockers =
  blocker-gauge-domain-descent-unproved
  ∷ blocker-quotient-symmetry-unproved
  ∷ blocker-self-adjointness-unproved
  ∷ blocker-ym-clay-forbidden
  ∷ []

gaugeQuotientDescentBlockerCount : Nat
gaugeQuotientDescentBlockerCount =
  listLength canonicalGaugeQuotientDescentBlockers

gaugeQuotientDescentBlockerCountIs4 :
  gaugeQuotientDescentBlockerCount ≡ 4
gaugeQuotientDescentBlockerCountIs4 = refl

GaugeQuotientDescentTheoremProvedLightweight : Bool
GaugeQuotientDescentTheoremProvedLightweight = false

GaugeQuotientDescentTheoremProvedLightweightIsFalse :
  GaugeQuotientDescentTheoremProvedLightweight ≡ false
GaugeQuotientDescentTheoremProvedLightweightIsFalse = refl

record YMKillingBoundaryGaugeQuotientDescentLightweightBoundary : Set where
  field
    clauses : List GaugeQuotientDescentClause
    clausesAreCanonical : clauses ≡ canonicalGaugeQuotientDescentClauses
    invariants : List GaugeQuotientInvariant
    invariantsAreCanonical : invariants ≡ canonicalGaugeQuotientInvariants
    blockers : List GaugeQuotientDescentBlocker
    blockersAreCanonical : blockers ≡ canonicalGaugeQuotientDescentBlockers
    clauseCountIs8 : gaugeQuotientDescentClauseCount ≡ 8
    invariantCountIs4 : gaugeQuotientInvariantCount ≡ 4
    blockerCountIs4 : gaugeQuotientDescentBlockerCount ≡ 4
    theoremStillFalse : GaugeQuotientDescentTheoremProvedLightweight ≡ false

canonicalYMKillingBoundaryGaugeQuotientDescentLightweightBoundary :
  YMKillingBoundaryGaugeQuotientDescentLightweightBoundary
canonicalYMKillingBoundaryGaugeQuotientDescentLightweightBoundary =
  record
    { clauses = canonicalGaugeQuotientDescentClauses
    ; clausesAreCanonical = refl
    ; invariants = canonicalGaugeQuotientInvariants
    ; invariantsAreCanonical = refl
    ; blockers = canonicalGaugeQuotientDescentBlockers
    ; blockersAreCanonical = refl
    ; clauseCountIs8 = refl
    ; invariantCountIs4 = refl
    ; blockerCountIs4 = refl
    ; theoremStillFalse = refl
    }

YMGaugeQuotientDescentLightweightBoundaryRecorded : Bool
YMGaugeQuotientDescentLightweightBoundaryRecorded = true

YMGaugeQuotientDescentLightweightBoundaryRecordedIsTrue :
  YMGaugeQuotientDescentLightweightBoundaryRecorded ≡ true
YMGaugeQuotientDescentLightweightBoundaryRecordedIsTrue = refl
