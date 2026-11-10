module DASHI.Physics.Foundations.KakeyaYMAllScaleSameSourceComparisonExact where

------------------------------------------------------------------------
-- SOURCE: BalabanRGTwoMetricUniformComparisonExact already proves
-- the complete one-step division-free physical transport inequality.
-- This module proves the ALL-SCALE indexed same-state consumption
-- with the SAME observer, context and address pair at each scale.
--
-- The scale-indexed witness IS NOT CONSTRUCTED from p-adic topology.
-- In particular, an all-scales comparison with positive, uniform,
-- nonzero constants cannot be inferred merely from cylinder addresses.
--
-- Original Kakeya authors: Wang--Zahl (2025), Guth--Wang--Zahl
-- (2026). No Kakeya dimensional theorem is reproved or asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; _*_; _+_; _≤_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.YangMills.BalabanRGTwoMetricUniformComparisonExact as RG
import DASHI.Physics.Foundations.KakeyaYMUltrametricPhysicalComparisonExact as Prior

record SameObjectAllScaleComparison : Set₁ where
  field
    PhysicalState : Set
    Context : Set
    Address : Set
    selectedState : PhysicalState
    selectedContext : Context
    selectedAddress : Nat → PhysicalState → Context → Address

    -- Full physical and refinement distances are indexed by a
    -- common scale, one actual state, and one actual context.
    physicalDistance : Nat → PhysicalState → PhysicalState → ℚ
    refinementDistance : Nat → Address → Address → ℚ

    -- A scale-specific step is actual source input; do not fabricate
    -- physical comparability from an ultrametric code alone.
    step : Nat → PhysicalState → PhysicalState → RG.RGTwoMetricStep

    samePhysicalDistance :
      ∀ n x y →
      RG.physicalDistance (step n x y) ≡ physicalDistance n x y

    samePhysicalDistanceNext :
      ∀ n x y →
      RG.physicalDistanceNext (step n x y)
        ≡ physicalDistance (suc n) x y

    sameRGDistance :
      ∀ n x y →
      RG.rgDistance (step n x y)
        ≡ refinementDistance n
            (selectedAddress n x selectedContext)
            (selectedAddress n y selectedContext)

    sameRGDistanceNext :
      ∀ n x y →
      RG.rgDistanceNext (step n x y)
        ≡ refinementDistance (suc n)
            (selectedAddress (suc n) x selectedContext)
            (selectedAddress (suc n) y selectedContext)

open SameObjectAllScaleComparison public

-- This is genuinely all-scale (forall n), and the selected physical
-- and address distances are definitionally those of the SAME source
-- step, rather than a duplicated certificate for another metric.
allScalePhysicalContraction :
  (s : SameObjectAllScaleComparison) →
  ∀ n x y →
  RG.comparisonLower (step s n x y) *
    physicalDistance s (suc n) x y
  ≤ RG.contraction (step s n x y) *
      RG.comparisonUpper (step s n x y) *
      physicalDistance s n x y
    + RG.physicalScale (step s n x y) *
      RG.reopeningError (step s n x y)
allScalePhysicalContraction s n x y
  rewrite sym (samePhysicalDistance s n x y)
        | sym (samePhysicalDistanceNext s n x y) =
  Prior.sameSelectedPhysicalMetricBound (step s n x y)

-- Exact same-state identity of the cylinder distance used by the
-- selected physical transport theorem, on the actual context slice.
allScaleRefinementIsOriginalAddress :
  (s : SameObjectAllScaleComparison) →
  ∀ n x y →
  RG.rgDistance (step s n x y)
  ≡ refinementDistance s n
      (selectedAddress s n x (selectedContext s))
      (selectedAddress s n y (selectedContext s))
allScaleRefinementIsOriginalAddress s = sameRGDistance s

allScaleNextRefinementIsOriginalAddress :
  (s : SameObjectAllScaleComparison) →
  ∀ n x y →
  RG.rgDistanceNext (step s n x y)
  ≡ refinementDistance s (suc n)
      (selectedAddress s (suc n) x (selectedContext s))
      (selectedAddress s (suc n) y (selectedContext s))
allScaleNextRefinementIsOriginalAddress s = sameRGDistanceNext s

-- Terminal aggregation without choosing a different observer metric:
-- all-scale inequality and both refinement-source identifications.
sameObjectAllScaleReceipt :
  (s : SameObjectAllScaleComparison) →
  ∀ n x y →
  (RG.comparisonLower (step s n x y) *
     physicalDistance s (suc n) x y
   ≤ RG.contraction (step s n x y) *
       RG.comparisonUpper (step s n x y) *
       physicalDistance s n x y
     + RG.physicalScale (step s n x y) *
       RG.reopeningError (step s n x y))
  ×
  (RG.rgDistance (step s n x y)
   ≡ refinementDistance s n
       (selectedAddress s n x (selectedContext s))
       (selectedAddress s n y (selectedContext s)))
sameObjectAllScaleReceipt s n x y =
  allScalePhysicalContraction s n x y ,
  allScaleRefinementIsOriginalAddress s n x y


-- A cutoff-independent comparison is stronger than a witness indexed by
-- n. It is a genuinely additional original-source obligation.
record UniformSameObjectComparison : Set₁ where
  field
    original : SameObjectAllScaleComparison
    fixedLower fixedUpper fixedContraction fixedScale fixedError : ℚ
    lowerIndependent : ∀ n x y →
      RG.comparisonLower (step original n x y) ≡ fixedLower
    upperIndependent : ∀ n x y →
      RG.comparisonUpper (step original n x y) ≡ fixedUpper
    contractionIndependent : ∀ n x y →
      RG.contraction (step original n x y) ≡ fixedContraction
    scaleIndependent : ∀ n x y →
      RG.physicalScale (step original n x y) ≡ fixedScale
    errorIndependent : ∀ n x y →
      RG.reopeningError (step original n x y) ≡ fixedError
open UniformSameObjectComparison public

-- No local re-derivation of the Balaban source inequality: all five
-- scale-parameter equalities are applied to the inherited theorem.
uniformAllScalePhysicalContraction :
  (u : UniformSameObjectComparison) →
  ∀ n x y →
  fixedLower u * physicalDistance (original u) (suc n) x y
  ≤ fixedContraction u * fixedUpper u *
      physicalDistance (original u) n x y
    + fixedScale u * fixedError u
uniformAllScalePhysicalContraction u n x y
  rewrite sym (lowerIndependent u n x y)
        | sym (upperIndependent u n x y)
        | sym (contractionIndependent u n x y)
        | sym (scaleIndependent u n x y)
        | sym (errorIndependent u n x y) =
  allScalePhysicalContraction (original u) n x y

-- IMPORTANT: this proves an actual all-scale *consequence* if the
-- uniformity proofs exist. No cutoff-independent bound is generated
-- from an arbitrary RG contraction sequence.
