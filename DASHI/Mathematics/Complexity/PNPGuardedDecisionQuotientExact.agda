module DASHI.Mathematics.Complexity.PNPGuardedDecisionQuotientExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.RecursiveHyperfabricQuotientExact as Q

-- A semantic decision observer must be attached to the same original
-- formula and actual candidate; a random-access serialization bit is
-- not an inhabitant of this interface by itself.
record GuardedQuery {cost : PR.PolynomialCostModel Cook.BooleanFormula}
  (candidate : Direct.PolynomialSATDeciderCandidate cost) : Set where
  field
    formula : Cook.BooleanFormula
    returned : Bool
    originalDecision : returned ≡ Direct.decide candidate formula
open GuardedQuery public

-- Explicitly separate the semantic negation from the resource theorem.
-- Neither is manufactured by the quotient section.
record DecisionNegation {cost : PR.PolynomialCostModel Cook.BooleanFormula}
  {candidate : Direct.PolynomialSATDeciderCandidate cost}
  (query : GuardedQuery candidate) : Set where
  field
    acceptedUnsat : returned query ≡ true → Cook.Satisfiable (formula query) → ⊥
    rejectedSat : returned query ≡ false → Cook.Satisfiable (formula query)
open DecisionNegation public

failure : ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
  {candidate : Direct.PolynomialSATDeciderCandidate cost}
  (query : GuardedQuery candidate) → DecisionNegation query →
  Direct.SATDecisionFailure candidate
failure query neg with returned query in eq
... | true = Direct.falsePositive (formula query)
  (trans (sym (originalDecision query)) eq) (acceptedUnsat neg eq)
... | false = Direct.falseNegative (formula query) (rejectedSat neg eq)
  (trans (sym (originalDecision query)) eq)

record SameHorizon (Physical : Nat → Set) (T : Nat) : Set where
  field
    paid : Nat
    actual : Physical paid
    fits : paid ≤ T

-- A valid quotient of the decision-observing carrier transports the
-- returned decision at every original configuration, not merely a label.
transportQuery : ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
  {candidate : Direct.PolynomialSATDeciderCandidate cost}
  {X K : Set} {observe : X → Bool} {reduced : K → Bool} →
  Q.QuotientStep X K Bool observe reduced →
  (f : Cook.BooleanFormula) → (x : X) →
  observe x ≡ Direct.decide candidate f → GuardedQuery candidate
transportQuery q f x e = record
  { formula = f
  ; returned = _ 
  ; originalDecision = trans (Q.closed q x) e
  }

-- Original candidate endpoint decision theorem is the donor for the
-- observe equality. The same-object Cook self-quotation that inhabits
-- DecisionNegation and SameHorizon is still a mathematical obligation.
