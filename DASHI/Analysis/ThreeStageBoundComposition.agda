module DASHI.Analysis.ThreeStageBoundComposition where

open import Agda.Primitive using (Level; _⊔_; lsuc)

------------------------------------------------------------------------
-- Generic composition of three multiplicative operator estimates.
--
-- This is deliberately independent of norms, matrices and real numbers.  A
-- concrete lane supplies a preorder, a scalar product used for bound constants,
-- and left monotonicity of that product.  The theorem then composes
--
--   stage01 x <= C01
--   stageR  x <= R0  * stage01 x
--   stage10 x <= C10 * stageR x
--   target x <= stage10 x
--
-- into
--
--   target x <= C10 * (R0 * C01).
------------------------------------------------------------------------

record MultiplicativeBoundLaws {s : Level} (Scalar : Set s) : Set (lsuc s) where
  field
    _≤_ : Scalar → Scalar → Set s
    _⊗_ : Scalar → Scalar → Scalar

    ≤-trans :
      ∀ {a b c} →
      a ≤ b →
      b ≤ c →
      a ≤ c

    multiplyMonotoneLeft :
      ∀ left {a b} →
      a ≤ b →
      (left ⊗ a) ≤ (left ⊗ b)

open MultiplicativeBoundLaws public

record ThreeStageBound
    {x s : Level}
    (Input : Set x)
    (Scalar : Set s)
    (L : MultiplicativeBoundLaws Scalar) : Set (lsuc (x ⊔ s)) where
  field
    target : Input → Scalar
    stage01 : Input → Scalar
    stageR : Input → Scalar
    stage10 : Input → Scalar

    c01 : Scalar
    r0 : Scalar
    c10 : Scalar

    targetToStage10 :
      ∀ input → _≤_ L (target input) (stage10 input)

    stage10Bound :
      ∀ input →
      _≤_ L
        (stage10 input)
        (_⊗_ L c10 (stageR input))

    resolventBound :
      ∀ input →
      _≤_ L
        (stageR input)
        (_⊗_ L r0 (stage01 input))

    stage01Bound :
      ∀ input → _≤_ L (stage01 input) c01

open ThreeStageBound public

threeStageProduct :
  ∀ {x s}
    {Input : Set x}
    {Scalar : Set s}
    {L : MultiplicativeBoundLaws Scalar} →
  ThreeStageBound Input Scalar L →
  Scalar
threeStageProduct {L = L} B =
  _⊗_ L (c10 B) (_⊗_ L (r0 B) (c01 B))

threeStageBoundComposes :
  ∀ {x s}
    {Input : Set x}
    {Scalar : Set s}
    (L : MultiplicativeBoundLaws Scalar)
    (B : ThreeStageBound Input Scalar L)
    (input : Input) →
  _≤_ L (target B input) (threeStageProduct B)
threeStageBoundComposes L B input =
  ≤-trans L
    (targetToStage10 B input)
    (≤-trans L
      (stage10Bound B input)
      (multiplyMonotoneLeft L (c10 B)
        (≤-trans L
          (resolventBound B input)
          (multiplyMonotoneLeft L (r0 B) (stage01Bound B input)))))
