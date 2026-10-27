module DASHI.Arithmetic.TwinPrimeSixWheelExact where

------------------------------------------------------------------------
-- SOURCE ROOTS AND OWNERSHIP
--
-- Eratosthenes: elementary prime sieve.
-- Viggo Brun: twin-prime sieve and almost-prime bounds (1915-1920).
-- G. H. Hardy and J. E. Littlewood: prime-pair conjectures (1923).
-- Goldston, Pintz, Yildirim: small prime gaps (2005/2009).
-- Yitang Zhang: bounded gaps (2013; Annals 2014).
-- James Maynard and Terence Tao: multidimensional sieve (2013-2015).
-- DHJ Polymath: H_1 <= 246 (2014).
-- OpenAI / GPT-6 Astra: claimed H_1 <= 186 (2026), accompanying
--   conditional Lean proof with three explicit assumptions.
--
-- REUSE: canonical DASHI mod-six prime theorem, six-wheel partition
-- and exact CRT23 witnesses. Do not copy their proof bodies.
--
-- NEW DASHI PROOF: among six residue classes, r5 is exactly the class
-- where BOTH r and r+2 survive the {2,3} sieve. This is a NECESSARY
-- LOCAL FILTER, not a statement that either integer is prime.
--
-- The definitions of twin-prime infinitude and bounded prime pairs
-- are specifications. Only the implication from an assumed twin-prime
-- infinitude witness to bounded pairs is proved below.
--
-- No theorem here proves infinitely many twin primes, H_1 <= 186,
-- a prime-distribution estimate, or a consecutive-prime gap bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Primality as NatPrimality using (Prime)
open import Data.Product using (Σ; _×_; _,_)

import DASHI.Arithmetic.PrimeModSixSieveExact as PrimeModSix
import DASHI.Arithmetic.SixWheelSieveCountExact as Wheel
import DASHI.Arithmetic.SixWheelCRTExact as CRT

------------------------------------------------------------------------
-- The explicit +2 rotation on the six-element residue carrier.
------------------------------------------------------------------------

shiftTwo : Wheel.Residue6 → Wheel.Residue6
shiftTwo Wheel.r0 = Wheel.r2
shiftTwo Wheel.r1 = Wheel.r3
shiftTwo Wheel.r2 = Wheel.r4
shiftTwo Wheel.r3 = Wheel.r5
shiftTwo Wheel.r4 = Wheel.r0
shiftTwo Wheel.r5 = Wheel.r1

shiftTwoThreeTimes :
  (r : Wheel.Residue6) →
  shiftTwo (shiftTwo (shiftTwo r)) ≡ r
shiftTwoThreeTimes Wheel.r0 = refl
shiftTwoThreeTimes Wheel.r1 = refl
shiftTwoThreeTimes Wheel.r2 = refl
shiftTwoThreeTimes Wheel.r3 = refl
shiftTwoThreeTimes Wheel.r4 = refl
shiftTwoThreeTimes Wheel.r5 = refl

-- The CRT23 carrier has exact nonzero-mod-2 and nonzero-mod-3
-- proof witnesses. A surviving pair requires one witness at each
-- offset position. This is not a primality predicate.
PairWheelSurvivor : Wheel.Residue6 → Set
PairWheelSurvivor r =
  CRT.CRT23Survivor (CRT.r6ToCRT23 r)
  × CRT.CRT23Survivor (CRT.r6ToCRT23 (shiftTwo r))

r5PairSurvives : PairWheelSurvivor Wheel.r5
r5PairSurvives =
  CRT.r5SurvivesCRT , CRT.r1SurvivesCRT

-- Exhaustive six-case proof. Reuse the canonical excluded-class
-- impossibility theorem; do not reproduce its modular arithmetic.
pairSurvivorMustBeR5 :
  (r : Wheel.Residue6) →
  PairWheelSurvivor r →
  r ≡ Wheel.r5
pairSurvivorMustBeR5 Wheel.r0 (left , right) =
  ⊥-elim (CRT.excludedCannotSurviveCRT Wheel.e0 left)
pairSurvivorMustBeR5 Wheel.r1 (left , right) =
  ⊥-elim (CRT.excludedCannotSurviveCRT Wheel.e3 right)
pairSurvivorMustBeR5 Wheel.r2 (left , right) =
  ⊥-elim (CRT.excludedCannotSurviveCRT Wheel.e2 left)
pairSurvivorMustBeR5 Wheel.r3 (left , right) =
  ⊥-elim (CRT.excludedCannotSurviveCRT Wheel.e3 left)
pairSurvivorMustBeR5 Wheel.r4 (left , right) =
  ⊥-elim (CRT.excludedCannotSurviveCRT Wheel.e4 left)
pairSurvivorMustBeR5 Wheel.r5 (left , right) = refl

-- Existing arithmetic prime theorem, re-exported as an explicit
-- dependency. It does not by itself map a natural-number pair to
-- PairWheelSurvivor. That transport remains a separate obligation.
primeAboveThreeWheelClass :
  (n : Nat) →
  NatPrimality.Prime (4 + n) →
  PrimeModSix.PrimeModSixClass (4 + n)
primeAboveThreeWheelClass =
  PrimeModSix.primeAboveThreeModSix

------------------------------------------------------------------------
-- Specifications and a logically exact conditional implication.
------------------------------------------------------------------------

two : Nat
two = suc (suc zero)

TwinPrimeAt : Nat → Set
TwinPrimeAt n =
  NatPrimality.Prime n × NatPrimality.Prime (n + two)

TwinPrimesInfinitelyOften : Set
TwinPrimesInfinitelyOften =
  (lower : Nat) →
  Σ Nat (λ n → (lower ≤ n) × TwinPrimeAt n)

-- A bounded pair need not be consecutive. The separate converse
-- mapping to consecutive-prime gaps is NOT claimed here.
record BoundedPrimePair (bound start : Nat) : Set where
  constructor boundedPrimePair
  field
    shift : Nat
    shiftPositive : suc zero ≤ shift
    shiftWithinBound : shift ≤ bound
    startIsPrime : NatPrimality.Prime start
    endIsPrime : NatPrimality.Prime (start + shift)

InfinitelyManyBoundedPrimePairs : Nat → Set
InfinitelyManyBoundedPrimePairs bound =
  (lower : Nat) →
  Σ Nat (λ n → (lower ≤ n) × BoundedPrimePair bound n)

twinInfinitudeImpliesBoundedPairsTwo :
  TwinPrimesInfinitelyOften →
  InfinitelyManyBoundedPrimePairs two
twinInfinitudeImpliesBoundedPairsTwo twins lower
  with twins lower
... | n , (above , (leftPrime , rightPrime)) =
  n , (above ,
    boundedPrimePair
      two
      (s≤s z≤n)
      (s≤s (s≤s z≤n))
      leftPrime
      rightPrime)
