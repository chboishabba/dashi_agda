module DASHI.Foundations.NaryCyclicOutputPhaseCountExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163,
-- Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- DASHI CONTRIBUTION
--
-- Record the generic finite count behind the exact ternary phase quotient.
-- For an alphabet of size q = n+1 and a chosen q-cycle acting freely by
-- postcomposition on all endomorphism tables:
--
--   q^q = q * q^(q-1)
--   q!  = q * (q-1)!
--
-- Thus the expected phase-quotient counts are q^(q-1) total classes and
-- (q-1)! reversible/unit classes. This module proves the arithmetic ledger;
-- it does not pretend to construct a generic Fin q carrier or a generic free
-- action. The q=3 action itself is constructed exactly in
-- TernaryEndomorphismPhaseQuotientExact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)

pow : Nat → Nat → Nat
pow base zero = 1
pow base (suc exponent) = base * pow base exponent

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

record NaryCyclicPhaseCount (predecessor : Nat) : Set where
  constructor naryCyclicPhaseCount
  field
    alphabetSize : Nat
    alphabetSizeIsSuccessor : alphabetSize ≡ suc predecessor
    endomorphismCount : Nat
    endomorphismCountExact :
      endomorphismCount ≡ pow alphabetSize alphabetSize
    phaseQuotientCount : Nat
    phaseQuotientCountExact :
      phaseQuotientCount ≡ pow alphabetSize predecessor
    endomorphismFactorization :
      endomorphismCount ≡ alphabetSize * phaseQuotientCount
    reversibleCount : Nat
    reversibleCountExact :
      reversibleCount ≡ factorial alphabetSize
    reversiblePhaseQuotientCount : Nat
    reversiblePhaseQuotientCountExact :
      reversiblePhaseQuotientCount ≡ factorial predecessor
    reversibleFactorization :
      reversibleCount ≡ alphabetSize * reversiblePhaseQuotientCount

open NaryCyclicPhaseCount public

canonicalNaryCyclicPhaseCount :
  (predecessor : Nat) → NaryCyclicPhaseCount predecessor
canonicalNaryCyclicPhaseCount predecessor =
  naryCyclicPhaseCount
    (suc predecessor)
    refl
    (pow (suc predecessor) (suc predecessor))
    refl
    (pow (suc predecessor) predecessor)
    refl
    refl
    (factorial (suc predecessor))
    refl
    (factorial predecessor)
    refl
    refl

ternaryCount : NaryCyclicPhaseCount 2
ternaryCount = canonicalNaryCyclicPhaseCount 2

ternaryAlphabetIsThree : alphabetSize ternaryCount ≡ 3
ternaryAlphabetIsThree = refl

ternaryEndomorphismCountIsTwentySeven :
  endomorphismCount ternaryCount ≡ 27
ternaryEndomorphismCountIsTwentySeven = refl

ternaryPhaseQuotientCountIsNine :
  phaseQuotientCount ternaryCount ≡ 9
ternaryPhaseQuotientCountIsNine = refl

ternaryReversibleCountIsSix :
  reversibleCount ternaryCount ≡ 6
ternaryReversibleCountIsSix = refl

ternaryReversiblePhaseQuotientCountIsTwo :
  reversiblePhaseQuotientCount ternaryCount ≡ 2
ternaryReversiblePhaseQuotientCountIsTwo = refl

ternaryNonunitPhaseResidualIsSeven :
  2 + 7 ≡ phaseQuotientCount ternaryCount
ternaryNonunitPhaseResidualIsSeven = refl

record NaryCyclicPhaseCountBoundary : Set where
  field
    genericCountFactorizationConstructed : Bool
    genericCountFactorizationConstructedIsTrue :
      genericCountFactorizationConstructed ≡ true

    genericFiniteCyclicActionConstructedHere : Bool
    genericFiniteCyclicActionConstructedHereIsFalse :
      genericFiniteCyclicActionConstructedHere ≡ false

    ternaryExactActionConstructedElsewhere : Bool
    ternaryExactActionConstructedElsewhereIsTrue :
      ternaryExactActionConstructedElsewhere ≡ true

canonicalNaryCyclicPhaseCountBoundary : NaryCyclicPhaseCountBoundary
canonicalNaryCyclicPhaseCountBoundary =
  record
    { genericCountFactorizationConstructed = true
    ; genericCountFactorizationConstructedIsTrue = refl
    ; genericFiniteCyclicActionConstructedHere = false
    ; genericFiniteCyclicActionConstructedHereIsFalse = refl
    ; ternaryExactActionConstructedElsewhere = true
    ; ternaryExactActionConstructedElsewhereIsTrue = refl
    }
