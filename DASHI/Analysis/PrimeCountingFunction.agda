module DASHI.Analysis.PrimeCountingFunction where

-- Exact finite prime counting on Nat.
--
-- The primality decision procedure is supplied by a proof-bearing predicate.
-- The counter itself is executable and counts primes in the closed interval
-- [2 , n].  No asymptotic or analytic statement is built into this layer.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

record PrimePredicate : Set₁ where
  field
    Prime : Nat → Set
    prime? : (n : Nat) → Dec (Prime n)

primeIndicator : PrimePredicate → Nat → Nat
primeIndicator arithmetic n with PrimePredicate.prime? arithmetic n
... | yes _ = suc zero
... | no _ = zero

-- π(n): number of primes p with p ≤ n.  The recursion starts at 2 so the
-- intended count does not depend on separate proofs that 0 and 1 are nonprime.
primeCountLE : PrimePredicate → Nat → Nat
primeCountLE arithmetic zero = zero
primeCountLE arithmetic (suc zero) = zero
primeCountLE arithmetic (suc (suc n)) =
  primeIndicator arithmetic (suc (suc n))
  + primeCountLE arithmetic (suc n)

-- Number of primes strictly less than n.
primeCountLT : PrimePredicate → Nat → Nat
primeCountLT arithmetic zero = zero
primeCountLT arithmetic (suc n) = primeCountLE arithmetic n

primeCountStep :
  (arithmetic : PrimePredicate) →
  (n : Nat) →
  primeCountLE arithmetic (suc (suc n))
  ≡
  (primeIndicator arithmetic (suc (suc n))
   + primeCountLE arithmetic (suc n))
primeCountStep arithmetic n = refl

primeCountAtPrime :
  (arithmetic : PrimePredicate) →
  (n : Nat) →
  PrimePredicate.Prime arithmetic (suc (suc n)) →
  primeCountLE arithmetic (suc (suc n))
  ≡ suc (primeCountLE arithmetic (suc n))
primeCountAtPrime arithmetic n primeWitness
  with PrimePredicate.prime? arithmetic (suc (suc n))
... | yes _ = refl
... | no notPrime = ⊥-elim (notPrime primeWitness)

primeCountAtNonprime :
  (arithmetic : PrimePredicate) →
  (n : Nat) →
  (PrimePredicate.Prime arithmetic (suc (suc n)) → ⊥) →
  primeCountLE arithmetic (suc (suc n))
  ≡ primeCountLE arithmetic (suc n)
primeCountAtNonprime arithmetic n notPrimeWitness
  with PrimePredicate.prime? arithmetic (suc (suc n))
... | yes primeWitness = ⊥-elim (notPrimeWitness primeWitness)
... | no _ = refl

------------------------------------------------------------------------
-- Executable prime enumeration and exact cardinality
------------------------------------------------------------------------

primesUpTo : PrimePredicate → Nat → List Nat
primesUpTo arithmetic zero = []
primesUpTo arithmetic (suc zero) = []
primesUpTo arithmetic (suc (suc n))
  with PrimePredicate.prime? arithmetic (suc (suc n))
... | yes _ = suc (suc n) ∷ primesUpTo arithmetic (suc n)
... | no _ = primesUpTo arithmetic (suc n)

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

congNat :
  (f : Nat → Nat) →
  {x y : Nat} →
  x ≡ y →
  f x ≡ f y
congNat f refl = refl

primeListCountExact :
  (arithmetic : PrimePredicate) →
  (n : Nat) →
  listLength (primesUpTo arithmetic n)
  ≡ primeCountLE arithmetic n
primeListCountExact arithmetic zero = refl
primeListCountExact arithmetic (suc zero) = refl
primeListCountExact arithmetic (suc (suc n))
  with PrimePredicate.prime? arithmetic (suc (suc n))
... | yes _ =
  congNat suc (primeListCountExact arithmetic (suc n))
... | no _ =
  primeListCountExact arithmetic (suc n)

------------------------------------------------------------------------
-- Symmetric endpoint convention π₀(n)
------------------------------------------------------------------------

-- Twice the symmetric count avoids introducing rationals and directly matches
-- the left/right-limit definition:
--
--   2 π₀(n) = π(n⁻) + π(n).
--
-- At a prime endpoint the value is odd, encoding the half jump.
primeCountSymmetricTwice : PrimePredicate → Nat → Nat
primeCountSymmetricTwice arithmetic n =
  primeCountLT arithmetic n + primeCountLE arithmetic n

primeCountSymmetricTwiceDefinition :
  (arithmetic : PrimePredicate) →
  (n : Nat) →
  primeCountSymmetricTwice arithmetic n
  ≡
  (primeCountLT arithmetic n + primeCountLE arithmetic n)
primeCountSymmetricTwiceDefinition arithmetic n = refl

record PrimeCountingFiniteBoundary : Set where
  field
    exactNatCountOnly : ⊤
    symmetricEndpointEncodedByDoubling : ⊤
    symmetricValueUsesLeftRightCounts : ⊤
    noRealArgumentExtension : ⊤
    noPrimeNumberTheoremClaim : ⊤
    noRiemannExplicitFormulaClaim : ⊤
    noRiemannHypothesisPromotion : ⊤

primeCountingFiniteBoundary : PrimeCountingFiniteBoundary
primeCountingFiniteBoundary = record
  { exactNatCountOnly = tt
  ; symmetricEndpointEncodedByDoubling = tt
  ; symmetricValueUsesLeftRightCounts = tt
  ; noRealArgumentExtension = tt
  ; noPrimeNumberTheoremClaim = tt
  ; noRiemannExplicitFormulaClaim = tt
  ; noRiemannHypothesisPromotion = tt
  }
