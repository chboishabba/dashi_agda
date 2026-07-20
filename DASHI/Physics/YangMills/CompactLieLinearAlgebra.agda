module DASHI.Physics.YangMills.CompactLieLinearAlgebra where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_)
open import DASHI.Physics.YangMills.CompactLieGroupCore

------------------------------------------------------------------------
-- Real-linear structure missing from the minimal additive Lie-algebra carrier.
------------------------------------------------------------------------

record RealLieAlgebra
    {a : Level}
    (𝔤 : Set a)
    (L : LieAlgebra 𝔤) : Set (lsuc a) where
  field
    scale : ℝ → 𝔤 → 𝔤

    scaleZeroScalar : ∀ X → scale 0ℝ X ≡ zero L
    scaleOneScalar : ∀ X → scale 1ℝ X ≡ X
    scaleAddVectors : ∀ scalar X Y →
      scale scalar (add L X Y) ≡ add L (scale scalar X) (scale scalar Y)
    scaleAddScalars : ∀ left right X →
      scale (left +ℝ right) X
      ≡ add L (scale left X) (scale right X)
    scaleAssociative : ∀ left right X →
      scale (left *ℝ right) X
      ≡ scale left (scale right X)

    bracketScaleLeft : ∀ scalar X Y →
      bracket L (scale scalar X) Y ≡ scale scalar (bracket L X Y)
    bracketScaleRight : ∀ scalar X Y →
      bracket L X (scale scalar Y) ≡ scale scalar (bracket L X Y)

open RealLieAlgebra public

record AdjointLinearAction
    {g a : Level}
    {G : Set g} {𝔤 : Set a}
    (H : Group G)
    (L : LieAlgebra 𝔤)
    (R : RealLieAlgebra 𝔤 L) : Set (lsuc (g ⊔ a)) where
  field
    Ad : G → 𝔤 → 𝔤
    adjointIdentity : ∀ X → Ad (identity H) X ≡ X
    adjointProduct : ∀ x y X → Ad (multiply H x y) X ≡ Ad x (Ad y X)
    adjointAdd : ∀ x X Y → Ad x (add L X Y) ≡ add L (Ad x X) (Ad x Y)
    adjointScale : ∀ x scalar X → Ad x (scale R scalar X) ≡ scale R scalar (Ad x X)
    adjointBracket : ∀ x X Y →
      Ad x (bracket L X Y) ≡ bracket L (Ad x X) (Ad x Y)

open AdjointLinearAction public
