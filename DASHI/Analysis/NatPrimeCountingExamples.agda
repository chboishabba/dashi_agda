module DASHI.Analysis.NatPrimeCountingExamples where

-- Small normalization regressions for the concrete standard-library instance.
-- The prime enumeration is descending because the finite scan prepends each
-- newly encountered endpoint prime.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import DASHI.Analysis.NatPrimeCountingInstance

pi10 : natPrimeCountLE 10 ≡ 4
pi10 = refl

pi30 : natPrimeCountLE 30 ≡ 10
pi30 = refl

pi60 : natPrimeCountLE 60 ≡ 17
pi60 = refl

primesThrough10 :
  natPrimesUpTo 10 ≡ 7 ∷ 5 ∷ 3 ∷ 2 ∷ []
primesThrough10 = refl

-- π(5) = 3 and 5 is prime, hence 2π₀(5) = 5.
pi0TwiceAtPrime5 : natPrimeCountSymmetricTwice 5 ≡ 5
pi0TwiceAtPrime5 = refl

-- π(6) = 3 and 6 is not prime, hence 2π₀(6) = 6.
pi0TwiceAtComposite6 : natPrimeCountSymmetricTwice 6 ≡ 6
pi0TwiceAtComposite6 = refl
