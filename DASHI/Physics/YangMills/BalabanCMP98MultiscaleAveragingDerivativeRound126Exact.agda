{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact where

------------------------------------------------------------------------
-- ROUND126 A1: ONE-STEP CMP98 Q' -> MULTISCALE Q_k'
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- CMP98 writes the k-step linearized averaging as a finite composition of the
-- one-step averages.  Therefore after the literal one-step background derivative
-- has been calculated, the multiscale derivative is not a new analytic theorem:
-- it is the ordinary finite product rule
--
--   D(Q_{n-1} ... Q_0)
--     = sum_j Q_{n-1} ... Q_{j+1} (DQ_j) Q_{j-1} ... Q_0.
--
-- This module encodes that product rule recursively on the exact operator
-- carrier.  No commutativity is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record AdditiveOperatorCarrier : Set₁ where
  field
    Vector : Set
    zeroV : Vector
    addV : Vector → Vector → Vector

open AdditiveOperatorCarrier public

Operator : AdditiveOperatorCarrier → Set
Operator C = Vector C → Vector C

identityOperator : ∀ C → Operator C
identityOperator C x = x

zeroOperator : ∀ C → Operator C
zeroOperator C _ = zeroV C

addOperator : ∀ C → Operator C → Operator C → Operator C
addOperator C left right x = addV C (left x) (right x)

compose : ∀ C → Operator C → Operator C → Operator C
compose C outer inner x = outer (inner x)

record OneStepAveragingDerivative (C : AdditiveOperatorCarrier) : Set₁ where
  field
    q qPrime : Nat → Operator C

open OneStepAveragingDerivative public

-- Q_n = q_{n-1} ... q_0.
multiscaleAverage :
  ∀ {C} → OneStepAveragingDerivative C → Nat → Operator C
multiscaleAverage {C} dataSet zero = identityOperator C
multiscaleAverage {C} dataSet (suc n) =
  compose C (q dataSet n) (multiscaleAverage dataSet n)

-- Recursive product rule.  This is exactly the insertion sum, with the newest
-- derivative insertion separated from the older insertions.
multiscaleAveragePrime :
  ∀ {C} → OneStepAveragingDerivative C → Nat → Operator C
multiscaleAveragePrime {C} dataSet zero = zeroOperator C
multiscaleAveragePrime {C} dataSet (suc n) =
  addOperator C
    (compose C (qPrime dataSet n) (multiscaleAverage dataSet n))
    (compose C (q dataSet n) (multiscaleAveragePrime dataSet n))

record LiteralComposedAveragingDerivative
    {C : AdditiveOperatorCarrier}
    (dataSet : OneStepAveragingDerivative C) : Set₁ where
  field
    literalQ literalQPrime : Nat → Operator C

    literalQZero : literalQ zero ≡ identityOperator C
    literalQStep : ∀ n →
      literalQ (suc n)
      ≡ compose C (q dataSet n) (literalQ n)

    literalQPrimeZero : literalQPrime zero ≡ zeroOperator C
    literalQPrimeStep : ∀ n →
      literalQPrime (suc n)
      ≡ addOperator C
          (compose C (qPrime dataSet n) (literalQ n))
          (compose C (q dataSet n) (literalQPrime n))

open LiteralComposedAveragingDerivative public

-- Once the literal family uses exactly the same recursive source composition,
-- its values agree with the canonical finite product.  Equality is stated
-- pointwise so no function-extensionality axiom is needed.
literalMultiscaleAveragePointwise :
  ∀ {C} {dataSet : OneStepAveragingDerivative C}
    (literal : LiteralComposedAveragingDerivative dataSet) n x →
  literalQ literal n x ≡ multiscaleAverage dataSet n x
literalMultiscaleAveragePointwise literal zero x
  rewrite literalQZero literal = refl
literalMultiscaleAveragePointwise {C} {dataSet} literal (suc n) x
  rewrite literalQStep literal n
        | literalMultiscaleAveragePointwise literal n x = refl

literalMultiscaleAveragePrimePointwise :
  ∀ {C} {dataSet : OneStepAveragingDerivative C}
    (literal : LiteralComposedAveragingDerivative dataSet) n x →
  literalQPrime literal n x ≡ multiscaleAveragePrime dataSet n x
literalMultiscaleAveragePrimePointwise literal zero x
  rewrite literalQPrimeZero literal = refl
literalMultiscaleAveragePrimePointwise {C} {dataSet} literal (suc n) x
  rewrite literalQPrimeStep literal n
        | literalMultiscaleAveragePointwise literal n x
        | literalMultiscaleAveragePrimePointwise literal n x = refl

cmp98MultiscaleAveragingProductRuleRound126Level : ProofLevel
cmp98MultiscaleAveragingProductRuleRound126Level = machineChecked

-- Highest-alpha source leaf is therefore one-step, not k-step: differentiate
-- the literal CMP98 one-step formula (including its g(ad Y), inverse-g factors
-- and parallel transports).  This module propagates that derivative through the
-- full finite blocking composition automatically.
literalCMP98OneStepAveragingDerivativeRound126Level : ProofLevel
literalCMP98OneStepAveragingDerivativeRound126Level = conditional
