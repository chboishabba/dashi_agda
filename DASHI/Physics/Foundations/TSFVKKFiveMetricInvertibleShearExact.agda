{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSFVKKFiveMetricInvertibleShearExact where

------------------------------------------------------------------------
-- P02/P08: 5D KK SIGNATURE IS A TRUE METRIC CONGRUENCE.
--
-- The existing exact selected KK bilinear is
--
--   G5((v,s),(w,t)) = g4(v,w)+b²(s+A(v))(t+A(w)).
--
-- Its offdiagonal A-terms are not new time axes: the ACTUAL invertible
-- linear KK shear (v,s) |-> (v,s+A(v)) takes the 5D metric to the
-- decoupled product (g4 ⊕ b²). Its inverse is source-constructed.
--
-- This proves an exact pointwise congruence for *every supplied* g4,
-- connection A and b² (including nonzero A), not merely a 3+1 count.
-- With an actually nondegenerate 3+1 g4, a physically positive b²
-- and justified Sylvester/index authority, the candidate has 4+1
-- Lorentzian signature and the same horizontal time direction.
--
-- This file DOES NOT supply nondegeneracy, physical positive radion,
-- global bundle transition maps, actual 5D Einstein action, smoothness,
-- or the observer->g4 source. Those are real P02/P08 missing inputs.
-- Attribution: Kaluza/Klein, original DASHI KK #1239/#1241 and
-- the new exact same-metric horizontal Schur owner.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Physics.Foundations.TSFVKKSelectedHorizontalMetricSchurExact
  as Horizontal

FiveTangent : Set → Set
FiveTangent V = V × ℚ

kkMetricShear :
  ∀ {V : Set} →
  (A : V → ℚ) → FiveTangent V → FiveTangent V
kkMetricShear A (v , s) = v , (s + A v)

kkMetricUnShear :
  ∀ {V : Set} →
  (A : V → ℚ) → FiveTangent V → FiveTangent V
kkMetricUnShear A (v , s) = v , (s - A v)

kkShearLeftInverse :
  ∀ {V : Set} (A : V → ℚ) (state : FiveTangent V) →
  kkMetricUnShear A (kkMetricShear A state) ≡ state
kkShearLeftInverse A (v , s) =
  cong (λ q → v , q) (Ring.solve-∀ s (A v))

kkShearRightInverse :
  ∀ {V : Set} (A : V → ℚ) (state : FiveTangent V) →
  kkMetricShear A (kkMetricUnShear A state) ≡ state
kkShearRightInverse A (v , s) =
  cong (λ q → v , q) (Ring.solve-∀ s (A v))

kkDecoupledProductBilinear :
  ∀ {V : Set} →
  (g4 : V → V → ℚ) →
  ℚ → FiveTangent V → FiveTangent V → ℚ
kkDecoupledProductBilinear g4 b2 (v , s) (w , t) =
  g4 v w + b2 * (s * t)

kkActualFiveBilinear :
  ∀ {V : Set} →
  (g4 : V → V → ℚ) →
  (A : V → ℚ) →
  ℚ → FiveTangent V → FiveTangent V → ℚ
kkActualFiveBilinear g4 A b2 (v , s) (w , t) =
  Horizontal.KK5Bilinear g4 A b2 v s w t

-- All five-dimensional KK offdiagonal entries are exactly the
-- pullback of the decoupled g4+positive-fibre product by an
-- EXPLICIT INVERTIBLE coordinate shear.
kkActualFiveBilinearIsInvertibleShearPullback :
  ∀ {V : Set}
  (g4 : V → V → ℚ)
  (A : V → ℚ)
  (b2 : ℚ) (v w : FiveTangent V) →
  kkActualFiveBilinear g4 A b2 v w
  ≡
  kkDecoupledProductBilinear g4 b2
    (kkMetricShear A v)
    (kkMetricShear A w)
kkActualFiveBilinearIsInvertibleShearPullback
  g4 A b2 (v , s) (w , t) = refl

-- "Horizontal" means the KK connection shear removes the circle
-- coordinate. This exact identity includes *nontrivial* A.
kkHorizontalShearHasZeroCirclePart :
  ∀ {V : Set} (A : V → ℚ) (v : V) →
  proj₂
    (kkMetricShear A
      (v , Horizontal.horizontalCircleComponent A v))
  ≡ 0ℚ
kkHorizontalShearHasZeroCirclePart A v =
  Ring.solve-∀ (A v)

-- A global signature theorem needs a real symmetric nondegenerate
-- 4D metric, a positive radius and an actual smooth 5D manifold.
-- The algebraic invertible congruence itself is now source-written.
