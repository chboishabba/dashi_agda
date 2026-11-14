{-# OPTIONS --safe #-}
module DASHI.Physics.Gravity.KSW668KaluzaKleinSpacelikeFiberCausalExact where

------------------------------------------------------------------------
-- D1/D2: ORIGINAL RATIONAL LORENTZ / KK CAUSAL PROJECTION.
--
-- Standard spacelike-fibre KK ansatz (sign -++++) is
--   ds5² = ds4² + phi² (dy + A_mu dx_mu)²
-- with phi² >= 0. For any 5D causal tangent ds5² <= 0,
-- the projected 4D tangent necessarily satisfies ds4² <= 0.
--
-- The theorem is algebraic and applies pointwise to an arbitrary physical
-- gauge coupling represented by the fifth-coordinate scalar q. It is NOT
-- an Einstein-field-equation solution or a new KK transport mechanism.
--
-- Negative fibre signs, indefinite extra dimensions, nonlocal signalling,
-- and effective metrics different from this ansatz require new hypotheses.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
import Data.Rational.Base as ℚ
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational

record SpacelikeKaluzaKleinCausalTangent : Set where
  constructor spacelike-kk-causal-tangent
  field
    baseLorentzIntervalSquared : ℚ
    gaugeCorrectedFiberVelocity : ℚ
    fiberRadiusSquared : ℚ
    fiberRadiusNonnegative : 0ℚ ≤ fiberRadiusSquared
    fiveDimensionalCausal :
      baseLorentzIntervalSquared
      + (fiberRadiusSquared
        * Rational.square gaugeCorrectedFiberVelocity)
      ≤ 0ℚ

open SpacelikeKaluzaKleinCausalTangent public

nonnegativeFiberEnergy :
  (radiusSquared q : ℚ) →
  0ℚ ≤ radiusSquared →
  0ℚ ≤ radiusSquared * Rational.square q
nonnegativeFiberEnergy radiusSquared q radiusNonnegative =
  let
    instance
      radiusNonNegative = ℚ.nonNegative radiusNonnegative
      velocitySquareNonNegative =
        ℚ.nonNegative (Rational.squareNonnegative q)
      energyNonNegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg radiusSquared (Rational.square q)
  in ℚₚ.nonNegative⁻¹ (radiusSquared * Rational.square q)

addNonnegativeCannotReduceInterval :
  (base fiber : ℚ) →
  0ℚ ≤ fiber →
  base ≤ base + fiber
addNonnegativeCannotReduceInterval base fiber nonnegative =
  subst
    (λ left → left ≤ base + fiber)
    (ℚₚ.+-identityʳ base)
    (ℚₚ.+-mono-≤ ℚₚ.≤-refl nonnegative)

originalKaluzaKleinCausalProjection :
  (v : SpacelikeKaluzaKleinCausalTangent) →
  baseLorentzIntervalSquared v ≤ 0ℚ
originalKaluzaKleinCausalProjection v =
  ℚₚ.≤-trans
    (addNonnegativeCannotReduceInterval
      (baseLorentzIntervalSquared v)
      (fiberRadiusSquared v
        * Rational.square (gaugeCorrectedFiberVelocity v))
      (nonnegativeFiberEnergy
        (fiberRadiusSquared v)
        (gaugeCorrectedFiberVelocity v)
        (fiberRadiusNonnegative v)))
    (fiveDimensionalCausal v)

-- Unit-fibre normalization is the conventional flat-KK special case:
-- any arbitrary q and any non-positive 5D interval project causally.
unitSpacelikeFiberProjection :
  (base q : ℚ) →
  base + Rational.square q ≤ 0ℚ →
  base ≤ 0ℚ
unitSpacelikeFiberProjection base q causal =
  ℚₚ.≤-trans
    (addNonnegativeCannotReduceInterval
      base (Rational.square q) (Rational.squareNonnegative q))
    causal

------------------------------------------------------------------------
-- Physical status: conditional local metric theorem and explicit no-go
-- for spacelike-fibre KK "shortcuts". Does not construct a 5D Einstein-
-- matter solution or claim measured travel. A causal 5D event with a
-- spacelike 4D projected tangent is inconsistent with THESE assumptions.
------------------------------------------------------------------------
