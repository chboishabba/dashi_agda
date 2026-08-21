module DASHI.Physics.Closure.NSAncientBlowupPeriodDecompactificationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Gabriel Koch; Nikolai Nadirashvili; Gregory A. Seregin;
--          Vladimir Sverak.
-- Title: "Liouville theorems for the Navier-Stokes equations and applications".
-- DOI: 10.1007/s11511-009-0039-6.
--
-- Authors: Zhen Lei; Xiao Ren; Qi S. Zhang.
-- Title: "A Liouville theorem for Axi-symmetric Navier-Stokes equations on
--         R^2 x T^1".
-- DOI: 10.1007/s00208-020-02128-9.
-- arXiv: 1911.01571.
--
-- PURPOSE
-- The fixed compact direction exploited by Lei-Ren-Zhang is not inherited
-- with fixed period by the standard singularity blow-up of a fixed torus.
-- If the original spatial period is L and the blow-up amplitude is M, then
-- y -> x0 + mu y with mu*M = 1 turns L-periodicity into (M*L)-periodicity.
-- Thus M -> infinity decompactifies a fixed torus locally.  This file proves
-- the exact algebraic period-transport statement; no analytic limit theorem
-- is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

PeriodicAt : {A : Set} → (ℚ → A) → ℚ → Set
PeriodicAt f L = (x : ℚ) → f (x + L) ≡ f x

rescaledSpatial : {A : Set} → (ℚ → A) → ℚ → ℚ → ℚ → A
rescaledSpatial f x0 mu y = f (x0 + mu * y)

inverseScaleMovesDilatedPeriodToOriginal :
  (mu M L : ℚ) →
  mu * M ≡ 1ℚ →
  mu * (M * L) ≡ L
inverseScaleMovesDilatedPeriodToOriginal mu M L scaleInverse =
  trans
    (solve (mu ∷ M ∷ L ∷ []))
    (trans
      (cong (_* L) scaleInverse)
      (ℚP.*-identityˡ L))

rescaledShiftMeaning :
  (x0 mu M L y : ℚ) →
  mu * M ≡ 1ℚ →
  x0 + mu * (y + M * L) ≡ (x0 + mu * y) + L
rescaledShiftMeaning x0 mu M L y scaleInverse =
  let
    distribute :
      x0 + mu * (y + M * L)
      ≡ (x0 + mu * y) + mu * (M * L)
    distribute = solve (x0 ∷ mu ∷ y ∷ M ∷ L ∷ [])

    periodMeaning : mu * (M * L) ≡ L
    periodMeaning = inverseScaleMovesDilatedPeriodToOriginal mu M L scaleInverse
  in
  trans distribute (cong ((x0 + mu * y) +_) periodMeaning)

blowupRescalingDilatesPeriod :
  {A : Set} →
  (f : ℚ → A) →
  (x0 mu M L : ℚ) →
  mu * M ≡ 1ℚ →
  PeriodicAt f L →
  PeriodicAt (rescaledSpatial f x0 mu) (M * L)
blowupRescalingDilatesPeriod f x0 mu M L scaleInverse periodic y =
  trans
    (cong f (rescaledShiftMeaning x0 mu M L y scaleInverse))
    (periodic (x0 + mu * y))

-- Three Cartesian periodic directions are transported independently by the
-- same one-dimensional algebra.  The analytic consequence M_k L -> infinity
-- is intentionally left to the real-analysis layer rather than encoded as a
-- Boolean receipt here.
