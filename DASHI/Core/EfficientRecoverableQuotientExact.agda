module DASHI.Core.EfficientRecoverableQuotientExact where

------------------------------------------------------------------------
-- EFFICIENT RECOVERABLE QUOTIENTS
--
-- Primary reference:
-- Sanjeev Arora and Boaz Barak,
-- "Computational Complexity: A Modern Approach", Cambridge University Press,
-- 2009. DOI: 10.1017/CBO9780511804090.
--
-- This module is complexity-theory-adjacent infrastructure.  It does not prove
-- P = NP or P /= NP.  It separates decision preservation, witness recovery,
-- receipt size, and explicit finite cost accounting.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_+_; _*_; _≤_)
open import Data.Empty using (⊥)

record WitnessProblem : Set₁ where
  constructor witnessProblem
  field
    Instance Witness : Set
    verifies : Instance → Witness → Set

open WitnessProblem public

record DecisionProjection (problem : WitnessProblem) : Set₁ where
  constructor decisionProjection
  field
    Coarse : Set
    project : Instance problem → Coarse
    coarseYes : Coarse → Set
    decisionForward : ∀ {x w} → verifies problem x w → coarseYes (project x)

open DecisionProjection public

record WitnessRecoverableQuotient (problem : WitnessProblem) : Set₁ where
  constructor witnessRecoverableQuotient
  field
    Coarse Receipt : Set
    project : Instance problem → Coarse
    receipt : Instance problem → Receipt
    reopenWitness : Coarse → Receipt → Witness problem
    reopeningVerifies : ∀ x → verifies problem x (reopenWitness (project x) (receipt x))

open WitnessRecoverableQuotient public

record ReopeningCost : Set where
  constructor reopeningCost
  field
    quotientCost receiptCost reopenCost : Nat
    totalCost : Nat
    totalCostAccounting : totalCost ≡ quotientCost + receiptCost + reopenCost

open ReopeningCost public

canonicalReopeningCost : Nat → Nat → Nat → ReopeningCost
canonicalReopeningCost q d r = reopeningCost q d r (q + d + r) refl

pow : Nat → Nat → Nat
pow n zero = 1
pow n (suc k) = n * pow n k

record PolynomialBound (cost : Nat → Nat) : Set where
  constructor polynomialBound
  field
    coefficient exponent : Nat
    bounded : ∀ n → cost n ≤ coefficient * pow (suc n) exponent

open PolynomialBound public

record EfficientRecoverableFamily : Set₁ where
  constructor efficientRecoverableFamily
  field
    quotientCost receiptConstructionCost reopeningCost receiptLength : Nat → Nat
    quotientPolynomial : PolynomialBound quotientCost
    receiptConstructionPolynomial : PolynomialBound receiptConstructionCost
    reopeningPolynomial : PolynomialBound reopeningCost
    receiptLengthPolynomial : PolynomialBound receiptLength

open EfficientRecoverableFamily public

record ComputationalModelCost : Set₁ where
  constructor computationalModelCost
  field
    Model State : Set
    reopenCostInModel : Model → State → Nat

open ComputationalModelCost public

record ModelCostSeparation (costs : ComputationalModelCost) : Set₁ where
  constructor modelCostSeparation
  field
    classical quantum : Model costs
    target : State costs
    classicalCost quantumCost : Nat
    classicalCostExact : reopenCostInModel costs classical target ≡ classicalCost
    quantumCostExact : reopenCostInModel costs quantum target ≡ quantumCost

open ModelCostSeparation public

data VerifierAuthority : Set where
  verificationOnly : VerifierAuthority

data WitnessConstructionFromVerifier : VerifierAuthority → Set where

verifierDoesNotConstructWitness : WitnessConstructionFromVerifier verificationOnly → ⊥
verifierDoesNotConstructWitness ()
