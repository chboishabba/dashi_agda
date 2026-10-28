module DASHI.Arithmetic.FiniteTwinSieveFactorableLiftExact where

------------------------------------------------------------------------
-- FINITE SIEVE PARITY / FACTORABLE-PAIR MAX-CUT
--
-- Classical sources: Eratosthenes, Brun, Selberg's parity obstruction,
-- DHJ Polymath (2014), Variants of the Selberg sieve...
-- Original DASHI owners:
--   CertifiedPrimePairModulusExact (true arithmetic finite pair test)
--   CertifiedPrimePairPeriodExact (allPairProductPeriodicMultiple)
--   FinitePrimeProductSieveExact (mixed-radix carrier distinct from CRT)
--
-- New: a constructive algebraic transformation taking ANY given
-- finite-sieve survivor r, product of sieving moduli P and t, to
--
--     L = r [1 + P(r+2)t]
--     L+2 = (r+2) [1 + Prt].
--
-- This is a double factorisation while preserving ALL finite pair
-- sieve filters by a previously PROVED product-period theorem.
-- It needs neither an arithmetic CRT inverse nor any analytic theorem.
--
-- At r>=2, P>=1 and t>=1, each displayed factor is >1. The Agda
-- source below proves the factorisations and survivor transport;
-- a global NonPrime conclusion and an unconditional construction of
-- a baseline r for every list are distinct remaining obligations.
-- This does NOT prove infinitely many twin primes (indeed it produces
-- composite candidates, once factor nontriviality is certified).
--
-- Signed SSP, Conway PRIMEGAME and Monster 3B/4B representation
-- owners retain their own code and proof authority. No same-object
-- or prime-distribution promotion.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; subst; trans; cong)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

import DASHI.Arithmetic.CertifiedPrimePairModulusExact as Pair
import DASHI.Arithmetic.CertifiedPrimePairPeriodExact as Period

-- The two multiplicative factors are explicit Nat expressions.
-- We intentionally do not call a factorisation with factor=1
-- a composite-number certificate.
leftFactor : Nat → Nat → Nat → Nat
leftFactor r P t = 1 + P * (r + 2) * t

rightFactor : Nat → Nat → Nat → Nat
rightFactor r P t = 1 + P * r * t

factorableLeft : Nat → Nat → Nat → Nat
factorableLeft r P t = r * leftFactor r P t

factorableRight : Nat → Nat → Nat → Nat
factorableRight r P t = (r + 2) * rightFactor r P t

sieveMultiplier : Nat → Nat → Nat → Nat
sieveMultiplier r P t = r * (r + 2) * t

-- Unlike an ad hoc large finite regression, these are polynomial
-- identities for ALL natural numbers r, P and t.
leftFactorisationGivesRightPlusTwo :
  (r P t : Nat) →
  factorableLeft r P t + 2 ≡ factorableRight r P t
leftFactorisationGivesRightPlusTwo =
  solve 3
    (λ r P t →
      (r :* (con 1 :+ ((P :* (r :+ con 2)) :* t))) :+ con 2
      :=
      (r :+ con 2) :* (con 1 :+ ((P :* r) :* t)))
    refl

factorableLeftIsProductPeriodShift :
  (r P t : Nat) →
  factorableLeft r P t ≡ r + sieveMultiplier r P t * P
factorableLeftIsProductPeriodShift =
  solve 3
    (λ r P t →
      r :* (con 1 :+ ((P :* (r :+ con 2)) :* t))
      :=
      r :+ ((((r :* (r :+ con 2)) :* t) :* P)))
    refl

-- Reuse the source's *actual arithmetic* finite sieve, not a
-- separate Boolean/SSP15-labelled surrogate.
factorablePairPreservesFiniteSieve :
  (axes : List Pair.CertifiedPrimeAxis) →
  (r t : Nat) →
  Pair.AllPairSurvive axes r →
  Pair.AllPairSurvive axes
    (factorableLeft r (Period.modulusProduct axes) t)
factorablePairPreservesFiniteSieve axes r t survivor =
  subst
    (Pair.AllPairSurvive axes)
    (sym (factorableLeftIsProductPeriodShift
      r (Period.modulusProduct axes) t))
    (Period.allPairProductPeriodicMultiple
      axes r
      (sieveMultiplier r (Period.modulusProduct axes) t)
      survivor)

-- The reverse follows from the existing BACKWARD period theorem:
-- the transformation does not gain any local residue information.
factorablePairReflectsFiniteSieve :
  (axes : List Pair.CertifiedPrimeAxis) →
  (r t : Nat) →
  Pair.AllPairSurvive axes
    (factorableLeft r (Period.modulusProduct axes) t) →
  Pair.AllPairSurvive axes r
factorablePairReflectsFiniteSieve axes r t survivor =
  Period.allPairProductPeriodicMultipleBack
    axes r (sieveMultiplier r (Period.modulusProduct axes) t)
    (subst
      (Pair.AllPairSurvive axes)
      (factorableLeftIsProductPeriodShift
        r (Period.modulusProduct axes) t)
      survivor)

-- A proof-carrying pair-of-products with no unspecified prime status.
record FactorableNeighbourPair (r P t : Nat) : Set where
  constructor factorableNeighbourPair
  field
    lower : Nat
    upper : Nat
    lowerProduct : lower ≡ r * leftFactor r P t
    upperProduct : upper ≡ (r + 2) * rightFactor r P t
    gapExactlyTwo : lower + 2 ≡ upper

open FactorableNeighbourPair public

canonicalFactorableNeighbourPair :
  (r P t : Nat) → FactorableNeighbourPair r P t
canonicalFactorableNeighbourPair r P t =
  factorableNeighbourPair
    (factorableLeft r P t)
    (factorableRight r P t)
    refl
    refl
    (leftFactorisationGivesRightPlusTwo r P t)

------------------------------------------------------------------------
-- EXPLICIT NONTRIVIAL FACTORS, ALL r>=2, P>=1, t>=1.
--
-- A factor of the form suc(suc k) is >1 by CONSTRUCTION. These
-- certificates are stronger than merely exhibiting n=a*b with a=1.
-- No primality decider, finite bound, or external analytic assumption.
------------------------------------------------------------------------

record TwoNontrivialFactors (n : Nat) : Set where
  constructor twoNontrivialFactors
  field
    firstResidual secondResidual : Nat
    productIsInput :
      n ≡ suc (suc firstResidual) * suc (suc secondResidual)

open TwoNontrivialFactors public

leftSecondResidual : Nat → Nat → Nat → Nat
leftSecondResidual a b c =
  b * (a + 4) * (suc c) + (a + 3) * (suc c) + c

rightSecondResidual : Nat → Nat → Nat → Nat
rightSecondResidual a b c =
  b * (a + 2) * (suc c) + (a + 1) * (suc c) + c

-- These are uniform explicit decompositions; the small-prime case
-- r=2 is covered rather than lost to an implicit positive-factor gate.
leftSecondFactorIsNontrivial :
  (a b c : Nat) →
  leftFactor (suc (suc a)) (suc b) (suc c)
    ≡ suc (suc (leftSecondResidual a b c))
leftSecondFactorIsNontrivial =
  solve 3
    (λ a b c →
      con 1 :+
        (((con 1 :+ b) :* (a :+ con 4)) :* (con 1 :+ c))
      :=
      con 2 :+
        (((b :* (a :+ con 4)) :* (con 1 :+ c))
          :+ (((a :+ con 3) :* (con 1 :+ c)) :+ c)))
    refl

rightSecondFactorIsNontrivial :
  (a b c : Nat) →
  rightFactor (suc (suc a)) (suc b) (suc c)
    ≡ suc (suc (rightSecondResidual a b c))
rightSecondFactorIsNontrivial =
  solve 3
    (λ a b c →
      con 1 :+
        (((con 1 :+ b) :* (a :+ con 2)) :* (con 1 :+ c))
      :=
      con 2 :+
        (((b :* (a :+ con 2)) :* (con 1 :+ c))
          :+ (((a :+ con 1) :* (con 1 :+ c)) :+ c)))
    refl

factorableLeftHasTwoNontrivialFactors :
  (a b c : Nat) →
  TwoNontrivialFactors
    (factorableLeft (suc (suc a)) (suc b) (suc c))
factorableLeftHasTwoNontrivialFactors a b c =
  twoNontrivialFactors
    a
    (leftSecondResidual a b c)
    (cong
      (λ z → suc (suc a) * z)
      (leftSecondFactorIsNontrivial a b c))

factorableRightHasTwoNontrivialFactors :
  (a b c : Nat) →
  TwoNontrivialFactors
    (factorableRight (suc (suc a)) (suc b) (suc c))
factorableRightHasTwoNontrivialFactors a b c =
  twoNontrivialFactors
    (a + 2)
    (rightSecondResidual a b c)
    (cong
      (λ z → (suc (suc a) + 2) * z)
      (rightSecondFactorIsNontrivial a b c))

-- Note: the output TWO certificates do NOT depend on a prime-pair
-- hypothesis. The finite sieve predicate can survive for both
-- nontrivially factorable endpoints.
