{-# OPTIONS --safe #-}

module DASHI.Arithmetic.TwinPrimeOddCompositeCubeRoughCutExact where

------------------------------------------------------------------------
-- CT15 PARITY / CUBE-ROUGNESS FINITE ARITHMETIC CUT.
--
-- If an integer has at least three (not necessarily distinct)
-- factors, all at least B, with the residual product at least 1,
-- then it is at least B^3.
--
-- In particular a negative-Mobius, squarefree composite has an
-- ODD number >=3 of distinct prime factors; its least factor
-- cubed is <= its value. The second assertion still needs the
-- ACTUAL prime-factorisation / Mobius readout in a separate module;
-- this file proves only its universal arithmetic heart.
--
-- Original maths: Euclid, basic multiplication order, Mobius parity.
-- This source is independently authored. Does not inherit analytic
-- shifted-prime cancellation from Lu-Wang-Wu (2026), nor imply twin
-- prime infinitude or Monster/Ibrahim/Pareto/QID same-object claims.
-- No ESD references or unsafe proof escapes.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
open import Data.Empty using (⊥)
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality using (subst; sym)

-- Deliberately the nested product shape used by prime factorisation.
cubeThreshold : Nat → Nat
cubeThreshold threshold =
  threshold * (threshold * (threshold * 1))

threeFactorsForceCubeBelow :
  (threshold a b c residualProduct : Nat) →
  threshold ≤ a →
  threshold ≤ b →
  threshold ≤ c →
  suc zero ≤ residualProduct →
  cubeThreshold threshold ≤ a * (b * (c * residualProduct))
threeFactorsForceCubeBelow threshold a b c residualProduct
    aBound bBound cBound residualPositive =
  NP.*-mono-≤ aBound
    (NP.*-mono-≤ bBound
      (NP.*-mono-≤ cBound residualPositive))

cubeBelowCertifiedTripleValue :
  (value threshold a b c residualProduct : Nat) →
  value ≡ a * (b * (c * residualProduct)) →
  threshold ≤ a →
  threshold ≤ b →
  threshold ≤ c →
  suc zero ≤ residualProduct →
  cubeThreshold threshold ≤ value
cubeBelowCertifiedTripleValue value threshold a b c residualProduct
    valueShape aBound bBound cBound residualPositive =
  subst (λ upper → cubeThreshold threshold ≤ upper)
    (sym valueShape)
    (threeFactorsForceCubeBelow threshold a b c residualProduct
      aBound bBound cBound residualPositive)

sucCannotBeBelowSelf : ∀ {n : Nat} → suc n ≤ n → ⊥
sucCannotBeBelowSelf {zero} ()
sucCannotBeBelowSelf {suc n} (s≤s smaller) =
  sucCannotBeBelowSelf smaller

-- A genuine cube-rough number cannot possess that triple factor
-- certificate. This is CONSTRUCTIVE and has no positivity-of-prime-
-- correlations assumption.
threeLargeFactorsContradictCubeRoughness :
  (value threshold a b c residualProduct : Nat) →
  value ≡ a * (b * (c * residualProduct)) →
  threshold ≤ a →
  threshold ≤ b →
  threshold ≤ c →
  suc zero ≤ residualProduct →
  value < cubeThreshold threshold →
  ⊥
threeLargeFactorsContradictCubeRoughness
    value threshold a b c residualProduct
    valueShape aBound bBound cBound residualPositive
    belowCube =
  sucCannotBeBelowSelf
    (NP.≤-trans belowCube
      (cubeBelowCertifiedTripleValue value threshold
        a b c residualProduct valueShape
        aBound bBound cBound residualPositive))
