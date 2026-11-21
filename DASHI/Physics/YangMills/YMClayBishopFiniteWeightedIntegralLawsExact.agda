{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayBishopFiniteWeightedIntegralLawsExact where

-- YM.REAL: actual finite weighted-list integration definitions.
-- This is a Setoid-algebra finite compiler; not an assumed Haar integral.
-- Source owner: Bishop real setoid + the positive SU2 Fejer cubature.
-- The concrete finite node list and its all-degree moment exactness are
-- separate producers and are NOT supplied here.
-- Attribution: Fejer, Stroud, Bishop/Murray/Csimma, Wilson/Balaban, DASHI.

open import Agda.Builtin.List using (List; []; _∷_)

record Weighted {Scalar Node : Set} (S : Set) : Set where
  constructor weighted
  field
    point : Node
    weight : Scalar
    weightEvidence : S
open Weighted public

module _
  {Scalar Node : Set}
  (_≈_ : Scalar → Scalar → Set)
  (zero one : Scalar)
  (_add_ _mul_ : Scalar → Scalar → Scalar)
  (refl≈ : ∀ x → x ≈ x)
  (trans≈ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z)
  (addCong : ∀ {x x' y y'} →
      x ≈ x' → y ≈ y' → (x add y) ≈ (x' add y'))
  (mulCong : ∀ {x x' y y'} →
      x ≈ x' → y ≈ y' → (x mul y) ≈ (x' mul y'))
  (mulOneRight : ∀ x → (x mul one) ≈ x)
  (Nonnegative : Scalar → Set)
  (zeroNonnegative : Nonnegative zero)
  (addNonnegative : ∀ {x y} →
      Nonnegative x → Nonnegative y → Nonnegative (x add y))
  (mulNonnegative : ∀ {x y} →
      Nonnegative x → Nonnegative y → Nonnegative (x mul y))
  (nonnegativeCong : ∀ {x y} → x ≈ y → Nonnegative x → Nonnegative y)
  where

  record WeightedNode : Set where
    constructor node
    field
      point : Node
      weight : Scalar
      nonnegativeWeight : Nonnegative weight
  open WeightedNode public

  sumWeights : List WeightedNode → Scalar
  sumWeights [] = zero
  sumWeights (x ∷ xs) =
    (weight x) add (sumWeights xs)

  integral : List WeightedNode → (Node → Scalar) → Scalar
  integral [] f = zero
  integral (x ∷ xs) f =
    (weight x mul f (point x)) add integral xs f

  integralRespects : ∀ xs f g →
    (∀ x → f x ≈ g x) →
    integral xs f ≈ integral xs g
  integralRespects [] f g fg = refl≈ zero
  integralRespects (x ∷ xs) f g fg =
    addCong
      (mulCong (refl≈ (weight x)) (fg (point x)))
      (integralRespects xs f g fg)

  integralConstantOne : ∀ xs →
    integral xs (λ _ → one) ≈ sumWeights xs
  integralConstantOne [] = refl≈ zero
  integralConstantOne (x ∷ xs) =
    addCong (mulOneRight (weight x))
      (integralConstantOne xs)

  integralNormalizedOne :
    ∀ xs → sumWeights xs ≈ one →
    integral xs (λ _ → one) ≈ one
  integralNormalizedOne xs normalized =
    trans≈ (integralConstantOne xs) normalized

  integralNonnegative : ∀ xs f →
    (∀ x → Nonnegative (f x)) →
    Nonnegative (integral xs f)
  integralNonnegative [] f nonnegative = zeroNonnegative
  integralNonnegative (x ∷ xs) f nonnegative =
    addNonnegative
      (mulNonnegative
        (nonnegativeWeight x)
        (nonnegative (point x)))
      (integralNonnegative xs f nonnegative)

  -- The finite source owner's normalization and positivity are derived
  -- from weights and algebra, not from an external integral oracle.
  -- Complete YM.REAL still needs:
  -- (i) actual Fejer/CII/circle nodes and all-degree weight identities;
  -- (ii) Bishop-real trig & their exactness;
  -- (iii) effective bn polynomial approximation and Cauchy limit;
  -- (iv) Wilson matrix/trace and original action identity, exp & Haar.
