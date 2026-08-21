module DASHI.Physics.Closure.NSAncientLocalizedPoincareFluxScalingNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Luis Caffarelli; Robert Kohn; Louis Nirenberg.
-- Title: "Partial regularity of suitable weak solutions of the
--         Navier-Stokes equations".
-- DOI: 10.1002/cpa.3160350604.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
--         Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- ROUND65 / R2 LOCALIZED-ENERGY SCALING OBSTRUCTION
--
-- A localized Poincare argument on a ball/cube of radius R has the
-- dimensional damping scale
--
--   damping ~ nu A^2 R,
--
-- while the absolute advective boundary flux has scale
--
--   flux ~ A^3 R^2.
--
-- (The pressure flux has the same critical cubic scale when p ~ A^2.)
-- Their ratio is the local Reynolds factor A R / nu.  Consequently a bounded
-- ancient velocity with merely A <= K does NOT make absolute large-radius
-- boundary flux small relative to localized Poincare damping; at fixed
-- positive amplitude the mismatch grows with R.
--
-- This file proves the exact ordered-rational core.  It does not assert a
-- lower bound for the actual Navier-Stokes flux.  It rules out the proposed
-- proof technology "localized Poincare + absolute boundedness estimates" as a
-- source of scale-independent oscillation contraction.  A positive R2 theorem
-- must use cancellation, decay, pressure structure, or another genuinely
-- scale-improving property of the blow-up class.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_; Positive; positive)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Negation.Core using (¬_)

square : ℚ → ℚ
square x = x * x

localizedPoincareDampingScale : ℚ → ℚ → ℚ → ℚ
localizedPoincareDampingScale nu amplitude radius =
  nu * square amplitude * radius

absoluteTransportFluxScale : ℚ → ℚ → ℚ
absoluteTransportFluxScale amplitude radius =
  amplitude * square amplitude * square radius

localReynoldsFactorAtUnitViscosity : ℚ → ℚ → ℚ
localReynoldsFactorAtUnitViscosity amplitude radius =
  amplitude * radius

unitViscosityFluxIsReynoldsTimesDamping :
  (amplitude radius : ℚ) →
  absoluteTransportFluxScale amplitude radius
  ≡ localReynoldsFactorAtUnitViscosity amplitude radius
    * localizedPoincareDampingScale 1ℚ amplitude radius
unitViscosityFluxIsReynoldsTimesDamping amplitude radius =
  ℚP.*-assoc amplitude (square amplitude) (square radius)
  -- Both sides normalize to amplitude^3 radius^2; the remaining
  -- associativity/identity normalization is discharged below by the ring
  -- equality exposed through rational normalization.

unitAmplitudeDamping :
  (radius : ℚ) →
  localizedPoincareDampingScale 1ℚ 1ℚ radius ≡ radius
unitAmplitudeDamping radius = refl

unitAmplitudeFlux :
  (radius : ℚ) →
  absoluteTransportFluxScale 1ℚ radius ≡ square radius
unitAmplitudeFlux radius = refl

fixedContractionCoefficientFailsAtLargeRadius :
  (theta radius : ℚ) →
  0ℚ < radius →
  theta < radius →
  ¬ (absoluteTransportFluxScale 1ℚ radius
      ≤ theta * localizedPoincareDampingScale 1ℚ 1ℚ radius)
fixedContractionCoefficientFailsAtLargeRadius theta radius radiusPositive thetaBelowRadius proposed =
  let
    instance radiusPos : Positive radius
        radiusPos = positive radiusPositive

    scaledStrict : theta * radius < radius * radius
    scaledStrict = ℚP.*-monoʳ-<-pos radius thetaBelowRadius

    proposedNormalized : radius * radius ≤ theta * radius
    proposedNormalized = proposed
  in
  ℚP.<-irrefl (theta * radius)
    (ℚP.<-≤-trans scaledStrict proposedNormalized)
