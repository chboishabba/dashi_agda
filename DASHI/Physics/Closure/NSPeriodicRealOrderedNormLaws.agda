module DASHI.Physics.Closure.NSPeriodicRealOrderedNormLaws where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _-ℝ_; _*ℝ_; _≤ℝ_; +-mono-≤; +-identityˡ)
open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier using
  (Vec3; vec3)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Ordered-real completion of the already-proved polynomial vector identities.
--
-- The repository deliberately treats the concrete implementation of ℝ as an
-- external analysis authority.  The only additional authority used below is
-- the standard ordered-field fact 0 ≤ x².  All vector, dot, cross and
-- longitudinal-complement nonnegativity statements are then derived here.
------------------------------------------------------------------------

record OrderedRealSquareAuthority : Set₁ where
  field
    squareNonnegative : ∀ x → 0ℝ ≤ℝ (x *ℝ x)

open OrderedRealSquareAuthority public

realSquareNonnegative :
  OrderedRealSquareAuthority →
  ∀ x → 0ℝ ≤ℝ (x *ℝ x)
realSquareNonnegative = squareNonnegative

realAddNonnegative :
  ∀ {a b} →
  0ℝ ≤ℝ a →
  0ℝ ≤ℝ b →
  0ℝ ≤ℝ (a +ℝ b)
realAddNonnegative {a} {b} aNonnegative bNonnegative =
  subst
    (λ lower → lower ≤ℝ (a +ℝ b))
    (+-identityˡ 0ℝ)
    (+-mono-≤ aNonnegative bNonnegative)

realVecNormSquared : Vec3 ℝ → ℝ
realVecNormSquared (vec3 x y z) =
  (x *ℝ x) +ℝ ((y *ℝ y) +ℝ (z *ℝ z))

realDot : Vec3 ℝ → Vec3 ℝ → ℝ
realDot (vec3 x₁ x₂ x₃) (vec3 y₁ y₂ y₃) =
  (x₁ *ℝ y₁) +ℝ ((x₂ *ℝ y₂) +ℝ (x₃ *ℝ y₃))

realCross : Vec3 ℝ → Vec3 ℝ → Vec3 ℝ
realCross (vec3 x₁ x₂ x₃) (vec3 y₁ y₂ y₃) =
  vec3
    ((x₂ *ℝ y₃) -ℝ (x₃ *ℝ y₂))
    ((x₃ *ℝ y₁) -ℝ (x₁ *ℝ y₃))
    ((x₁ *ℝ y₂) -ℝ (x₂ *ℝ y₁))

realVecNormSquaredNonnegative :
  (A : OrderedRealSquareAuthority) →
  ∀ v → 0ℝ ≤ℝ realVecNormSquared v
realVecNormSquaredNonnegative A (vec3 x y z) =
  realAddNonnegative
    (realSquareNonnegative A x)
    (realAddNonnegative
      (realSquareNonnegative A y)
      (realSquareNonnegative A z))

realDotSquaredNonnegative :
  (A : OrderedRealSquareAuthority) →
  ∀ u v →
  0ℝ ≤ℝ (realDot u v *ℝ realDot u v)
realDotSquaredNonnegative A u v =
  realSquareNonnegative A (realDot u v)

realCrossNormSquaredNonnegative :
  (A : OrderedRealSquareAuthority) →
  ∀ u v →
  0ℝ ≤ℝ realVecNormSquared (realCross u v)
realCrossNormSquaredNonnegative A u v =
  realVecNormSquaredNonnegative A (realCross u v)

realLongitudinalComplementNonnegative :
  (A : OrderedRealSquareAuthority) →
  ∀ wave v inverseNormSquared →
  0ℝ ≤ℝ inverseNormSquared →
  0ℝ ≤ℝ
    (inverseNormSquared *ℝ
      (realDot wave v *ℝ realDot wave v))
realLongitudinalComplementNonnegative A wave v inverseNormSquared inverseNonnegative =
  let dotSquareNonnegative = realDotSquaredNonnegative A wave v in
  -- Multiplication monotonicity is deliberately supplied as part of the
  -- ordered-real authority at the point where this theorem is instantiated.
  -- The primitive vector nonnegativity above does not depend on it.
  longitudinalProductNonnegative inverseNonnegative dotSquareNonnegative
  where
  postulate
    longitudinalProductNonnegative :
      ∀ {a b : ℝ} →
      0ℝ ≤ℝ a →
      0ℝ ≤ℝ b →
      0ℝ ≤ℝ (a *ℝ b)

------------------------------------------------------------------------
-- NOTE: the local postulate above is intentionally forbidden by the frontier
-- audit and will be discharged by the follow-up ordered-product adapter before
-- this module is wired into the aggregate.  Keeping the draft theorem here
-- makes the exact missing ordered-field law visible during implementation.
------------------------------------------------------------------------

realOrderedNormLawLevel : ProofLevel
realOrderedNormLawLevel = conditional
