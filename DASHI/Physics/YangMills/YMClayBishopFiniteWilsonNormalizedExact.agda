-- NOTE: source reuses transitive non-safe Bishop owners. This module is
-- intentionally not declared --safe until the source graph is migrated.
-- Actual Agda kernel check remains pending.
module DASHI.Physics.YangMills.YMClayBishopFiniteWilsonNormalizedExact where

-- YM.REAL: normalization on the ACTUAL Bishop real and inverse.
-- This is a FINITE weighted cylinder algebra. It uses a positive
-- partition witness derived elsewhere from the real Wilson action.
-- It is not a rebranding of an unproved physical Haar integral.
-- Original source remains YMClaySUNVariablePhysicalCutoffFamilyExact.
-- Attribution: Wilson/Balaban; Bishop/Murray/Csimma; DASHI original
-- finite source and P0 scalar owners.

open import Agda.Builtin.List using (List; []; _∷_)
import Real as B
import RealProperties as P
import Inverse as Inv
import DASHI.Physics.YangMills.YMClayP0BishopRealCarrierInstancesExact as P0

record WeightedConfiguration (Node : Set) : Set where
  constructor weightedConfiguration
  field
    point : Node
    weight : B.ℝ
open WeightedConfiguration public

module _ {Node : Set} where

  weightedSum :
    List (WeightedConfiguration Node) →
    (Node → B.ℝ) → B.ℝ
  weightedSum [] f = B.0ℝ
  weightedSum (x ∷ xs) f =
    B._+_
      (B._*_ (weight x) (f (point x)))
      (weightedSum xs f)

  weightedSumRespects :
    (nodes : List (WeightedConfiguration Node)) →
    (f g : Node → B.ℝ) →
    (∀ node → B._≃_ (f node) (g node)) →
    B._≃_ (weightedSum nodes f) (weightedSum nodes g)
  weightedSumRespects [] f g eq = P.≃-refl
  weightedSumRespects (x ∷ xs) f g eq =
    P.+-cong
      (P.*-cong P.≃-refl (eq (point x)))
      (weightedSumRespects xs f g eq)

  -- Any chosen finite Wilson density is integrated using the SAME
  -- finite weighted list; there is no independently supplied numerator.
  numerator :
    List (WeightedConfiguration Node) →
    (Node → B.ℝ) →
    (Node → B.ℝ) → B.ℝ
  numerator nodes density observable =
    weightedSum nodes (λ node → B._*_ (observable node) (density node))

  partition :
    List (WeightedConfiguration Node) →
    (Node → B.ℝ) → B.ℝ
  partition nodes density = numerator nodes density (λ _ → B.1ℝ)

  normalizedExpectation :
    (nodes : List (WeightedConfiguration Node)) →
    (density : Node → B.ℝ) →
    B._<_ B.0ℝ (partition nodes density) →
    (Node → B.ℝ) → B.ℝ
  normalizedExpectation nodes density positive observable =
    B._*_
      (numerator nodes density observable)
      (Inv._⁻¹ (partition nodes density)
        (P0.bishopPositiveDenominatorApartFromZero
          (partition nodes density) positive))

  normalizedExpectationOne :
    (nodes : List (WeightedConfiguration Node)) →
    (density : Node → B.ℝ) →
    (positive : B._<_ B.0ℝ (partition nodes density)) →
    B._≃_
      (normalizedExpectation nodes density positive (λ _ → B.1ℝ))
      B.1ℝ
  normalizedExpectationOne nodes density positive =
    let
      z = partition nodes density
      apart = P0.bishopPositiveDenominatorApartFromZero z positive
      inverse = Inv._⁻¹ z apart
    in
    P.≃-trans
      (P.*-comm z inverse)
      (Inv.*-inverseˡ z apart)

  normalizedExpectationRespects :
    (nodes : List (WeightedConfiguration Node)) →
    (density : Node → B.ℝ) →
    (positive : B._<_ B.0ℝ (partition nodes density)) →
    ∀ f g →
    (∀ node → B._≃_ (f node) (g node)) →
    B._≃_
      (normalizedExpectation nodes density positive f)
      (normalizedExpectation nodes density positive g)
  normalizedExpectationRespects nodes density positive f g eq =
    P.*-cong
      (weightedSumRespects nodes
        (λ node → B._*_ (f node) (density node))
        (λ node → B._*_ (g node) (density node))
        (λ node → P.*-cong (eq node) P.≃-refl))
      P.≃-refl

-- The strict positive partition must be proved from the ORIGINAL
-- Wilson exponential and an actually positive normalized product Haar.
-- The source must also identify its finite function-space carrier with
-- the finite Bishop quaternion link enumeration. Neither is asserted.
