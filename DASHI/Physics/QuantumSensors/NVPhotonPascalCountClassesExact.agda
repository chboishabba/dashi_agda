module DASHI.Physics.QuantumSensors.NVPhotonPascalCountClassesExact where

-- Standard Pascal/binomial recurrence (classical mathematical prior art).
-- This DASHI source reconstruction does not claim priority for Pascal's
-- triangle or the Bernoulli/binomial probability law. It is not yet a
-- proof that a filtered literal word list has that cardinality.
-- The definition is a count model for combinatorial words, not
-- a measured photon distribution or an assumed physical detector.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- C(n,k): number of bit words of length n with k clicks.
-- Boundary zero/successor cases encode the empty and nonempty words.
choose : Nat → Nat → Nat
choose zero zero = 1
choose zero (suc k) = 0
choose (suc n) zero = 1
choose (suc n) (suc k) = choose n k + choose n (suc k)

pascal : ∀ n k →
  choose (suc n) (suc k) ≡ choose n k + choose n (suc k)
pascal n k = refl

emptyCount : choose zero zero ≡ 1
emptyCount = refl

noPositiveCountAtZero : ∀ k → choose zero (suc k) ≡ 0
noPositiveCountAtZero k = refl

zeroClicks : ∀ n → choose (suc n) zero ≡ 1
zeroClicks n = refl

-- The existing Foundations.BishopExponentialBinomialCoefficientExact
-- owns the stdlib Data.Nat.Combinatorics (_C_) interface. A direct
-- equality choose n k ≡ n C k is an additional bridge obligation.
-- No extra probability ontology, quotient or opaque postulate.

-- In particular, these definitions do not supply a measured NV sensor,
-- an Agda kernel receipt, or authorisation to promote a hardware claim.
