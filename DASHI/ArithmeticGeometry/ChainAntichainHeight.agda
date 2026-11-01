module DASHI.ArithmeticGeometry.ChainAntichainHeight where

open import Agda.Builtin.Nat      using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma    using (Σ; _,_)
open import Agda.Builtin.Unit     using (⊤; tt)
open import Data.Nat              using (_≤_)

------------------------------------------------------------------------
-- DASHI height is not identified with canonical arithmetic height.
-- It is a structural proxy assembled from chain depth and antichain width.
------------------------------------------------------------------------

record OrderProfile : Set where
  constructor profile
  field
    chainDepth     : Nat
    antichainWidth : Nat

open OrderProfile public

record HeightWeights : Set where
  constructor weights
  field
    chainWeight     : Nat
    antichainWeight : Nat

open HeightWeights public

structuralHeight : HeightWeights → OrderProfile → Nat
structuralHeight w p =
  chainWeight w * chainDepth p +
  antichainWeight w * antichainWidth p

------------------------------------------------------------------------
-- A refinement is height-monotone when it does not decrease either axis.
------------------------------------------------------------------------

record Refines (p q : OrderProfile) : Set where
  field
    chain-mono     : chainDepth p ≤ chainDepth q
    antichain-mono : antichainWidth p ≤ antichainWidth q

------------------------------------------------------------------------
-- Arithmetic validation boundary.
--
-- canonicalHeight is supplied by an arithmetic backend (for example a
-- certified elliptic-curve or descent implementation).  DASHI may compare
-- its structural proxy against that value, but does not equate them by
-- definition.
------------------------------------------------------------------------

record ArithmeticHeightValidation (Point : Set) : Set₁ where
  field
    encode          : Point → OrderProfile
    canonicalHeight : Point → Nat
    weights         : HeightWeights

    lowerConstant upperConstant : Nat

    lower-bound :
      ∀ P → lowerConstant * structuralHeight weights (encode P)
          ≤ canonicalHeight P

    upper-bound :
      ∀ P → canonicalHeight P
          ≤ upperConstant * structuralHeight weights (encode P)

open ArithmeticHeightValidation public

------------------------------------------------------------------------
-- A finite structural-height bound supplies a finite-search receipt only
-- when a finite-fibre witness is provided.  This prevents the invalid move
-- from a small proxy value directly to arithmetic finiteness.
------------------------------------------------------------------------

record FiniteHeightFibre (Point : Set)
                         (V : ArithmeticHeightValidation Point)
                         (bound : Nat) : Set₁ where
  field
    Candidate : Set
    enumerate : Candidate → Point
    covers :
      ∀ P → structuralHeight (weights V) (encode V P) ≤ bound →
      Σ Candidate (λ c → enumerate c ≡ P)

------------------------------------------------------------------------
-- Search policy: increase arithmetic depth only while structural evidence
-- remains below the configured lift threshold.  Past the threshold, lift
-- invariants rather than blindly increasing coordinate bounds.
------------------------------------------------------------------------

record HeightLiftPolicy : Set where
  constructor heightPolicy
  field
    searchThreshold  : Nat
    descentThreshold : Nat

withinSearchBudget : HeightLiftPolicy → OrderProfile → HeightWeights → Set
withinSearchBudget policy p w =
  structuralHeight w p ≤ searchThreshold policy

requiresInvariantLift : HeightLiftPolicy → OrderProfile → HeightWeights → Set
requiresInvariantLift policy p w =
  descentThreshold policy ≤ structuralHeight w p
