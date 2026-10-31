module DASHI.Analysis.ZetaIrrationalFibreCommutingSquareBidiExact where

-- A new finite-stage bridge, not an irrational-real construction.
-- Source owners: DepthTwoNonaryResidueFibreExact (finite residue square),
-- QuadraticIrrationalSignedApproximationFibreExact (signed approximants),
-- PrimeCountingFunction (finite prime sieve).
-- The analytic limit and actual zeta interpretation are separate obligations.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Moonshine.DepthTwoNonaryResidueFibreExact as Nonary
import DASHI.Moonshine.QuadraticIrrationalSignedApproximationFibreExact as Irr
import DASHI.Analysis.PrimeCountingFunction as Prime

-- A commuting square over ANY finite-stage approximation carrier.
-- Its two paths must be definitionally or propositionally equal, not
-- inferred from matching numerical counts.
record StageCommutingSquare
    (Approximation Coarse Fine Observation : Set) : Set₁ where
  field
    toCoarse : Approximation → Coarse
    toFine : Approximation → Fine
    observeCoarse : Coarse → Observation
    observeFine : Fine → Observation
    commute : (x : Approximation) →
      observeCoarse (toCoarse x) ≡ observeFine (toFine x)
open StageCommutingSquare public

-- The downstream zeta/prime/counting observer can consume the
-- glued square consistently. This is a genuine path-independence
-- theorem but does not assume the observation is the analytic zeta.
squareConsumerAgreement :
  ∀ {A C F O Y : Set}
  (square : StageCommutingSquare A C F O)
  (consumer : O → Y) (x : A) →
  consumer (observeCoarse square (toCoarse square x))
  ≡ consumer (observeFine square (toFine square x))
squareConsumerAgreement square consumer x =
  cong consumer (commute square x)

-- Each consecutive time stage needs an explicit compatibility witness.
record CompatibleFibreHistory
    (Stage : Nat → Set) (readout : (n : Nat) → Stage n → Nat) : Set₁ where
  field
    at : (n : Nat) → Stage n
    coherent : (n : Nat) → readout n (at n) ≡ readout (n + 1) (at (n + 1))
open CompatibleFibreHistory public

-- A real-limit attachment is intentionally NOT generated from a finite
-- history. The Bishop-real carrier, modulus and identification must be
-- supplied by a producer. This blocks numerical/zeta same-object promotion.
record AnalyticLimitAttachment
    (Stage : Nat → Set) (Real : Set) : Set₁ where
  field
    stageValue : (n : Nat) → Stage n → Real
    limitValue : Real
    IsLimit : ((n : Nat) → Real) → Real → Set
    converges : (history : (n : Nat) → Stage n) →
      IsLimit (λ n → stageValue n (history n)) limitValue
open AnalyticLimitAttachment public

-- Existing exact prime-counting consumers are meaningful at each stage.
finitePrimeCount : Prime.PrimePredicate → Nat → Nat
finitePrimeCount = Prime.primeCountLE

finitePrimeCountIsUnchangedByEqualBound :
  (arithmetic : Prime.PrimePredicate) {m n : Nat} →
  m ≡ n → finitePrimeCount arithmetic m ≡ finitePrimeCount arithmetic n
finitePrimeCountIsUnchangedByEqualBound arithmetic refl = refl

-- A nontrivial exact finite sieve consumer on the staged history:
-- any two consecutive stages with equal retained readout have equal
-- *proof-bearing* prime counts, without claiming an analytic limit.
primeCountStableAcrossOneStep :
  ∀ {Stage : Nat → Set}
  {readout : (n : Nat) → Stage n → Nat} →
  (arithmetic : Prime.PrimePredicate) →
  (history : CompatibleFibreHistory Stage readout) →
  (n : Nat) →
  finitePrimeCount arithmetic (readout n (at history n))
  ≡ finitePrimeCount arithmetic
      (readout (n + 1) (at history (n + 1)))
primeCountStableAcrossOneStep arithmetic history n =
  cong (finitePrimeCount arithmetic) (coherent history n)

-- Two consecutive coherent charts glue without choosing another prime
-- counter. The proof composes existing equalities across the seam.
primeCountStableAcrossTwoSteps :
  ∀ {Stage : Nat → Set}
  {readout : (n : Nat) → Stage n → Nat} →
  (arithmetic : Prime.PrimePredicate) →
  (history : CompatibleFibreHistory Stage readout) →
  (n : Nat) →
  finitePrimeCount arithmetic (readout n (at history n))
  ≡ finitePrimeCount arithmetic
      (readout ((n + 1) + 1) (at history ((n + 1) + 1)))
primeCountStableAcrossTwoSteps arithmetic history n =
  trans (primeCountStableAcrossOneStep arithmetic history n)
        (primeCountStableAcrossOneStep arithmetic history (n + 1))
