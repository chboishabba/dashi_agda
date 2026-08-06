module DASHI.Physics.YangMills.BalabanP33DuhamelOrderedSimplexMeasureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Close the factor-of-two audit in the ordered-simplex formula for D^2 exp.
-- For one H/K ordering, the three telescoping coefficients are
--
--   1-s,  s-r,  r,       0 <= r <= s <= 1.
--
-- Their pointwise sum is one.  This module also integrates the three terms
-- separately, rather than merely naming the simplex area:
--
--   integral integral (1-s) dr ds = 1/6,
--   integral integral (s-r) dr ds = 1/6,
--   integral integral r     dr ds = 1/6.
--
-- Hence one ordering contributes exactly 1/2 of the constant majorant, and
-- the two H/K orderings contribute exactly one copy.  No factor two is lost or
-- gained between the pointwise telescope and the simplex measure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _-_; -_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

one half oneThird oneSixth : ℚ
one = + 1 / 1
half = + 1 / 2
oneThird = + 1 / 3
oneSixth = + 1 / 6

------------------------------------------------------------------------
-- Exact integration evaluator for a quadratic polynomial on [0,1].
--
--   integral_0^1 (constant + linear*s + quadratic*s^2) ds
--     = constant + linear/2 + quadratic/3.
------------------------------------------------------------------------

integrateUnitQuadratic : ℚ → ℚ → ℚ → ℚ
integrateUnitQuadratic constant linear quadratic =
  constant + half * linear + oneThird * quadratic

firstSegmentAfterInnerIntegration : ℚ → ℚ
firstSegmentAfterInnerIntegration scale =
  integrateUnitQuadratic (+ 0 / 1) scale (- scale)

middleSegmentAfterInnerIntegration : ℚ → ℚ
middleSegmentAfterInnerIntegration scale =
  integrateUnitQuadratic (+ 0 / 1) (+ 0 / 1) (half * scale)

lastSegmentAfterInnerIntegration : ℚ → ℚ
lastSegmentAfterInnerIntegration scale =
  integrateUnitQuadratic (+ 0 / 1) (+ 0 / 1) (half * scale)

firstSegmentIntegralExact : ∀ scale →
  firstSegmentAfterInnerIntegration scale ≡ oneSixth * scale
firstSegmentIntegralExact = ℚRing.solve-∀

middleSegmentIntegralExact : ∀ scale →
  middleSegmentAfterInnerIntegration scale ≡ oneSixth * scale
middleSegmentIntegralExact = ℚRing.solve-∀

lastSegmentIntegralExact : ∀ scale →
  lastSegmentAfterInnerIntegration scale ≡ oneSixth * scale
lastSegmentIntegralExact = ℚRing.solve-∀

oneOrderingIntegratedTelescope : ℚ → ℚ
oneOrderingIntegratedTelescope scale =
  firstSegmentAfterInnerIntegration scale
  + (middleSegmentAfterInnerIntegration scale
    + lastSegmentAfterInnerIntegration scale)

oneOrderingIntegratedTelescopeExact : ∀ scale →
  oneOrderingIntegratedTelescope scale ≡ half * scale
oneOrderingIntegratedTelescopeExact = ℚRing.solve-∀

orderedSimplexConstantIntegral : ℚ → ℚ
orderedSimplexConstantIntegral scale = half * scale

orderedSimplexAreaExact :
  orderedSimplexConstantIntegral one ≡ half
orderedSimplexAreaExact = ℚRing.solve []

------------------------------------------------------------------------
-- Two orderings in the symmetric second derivative.
------------------------------------------------------------------------

twoOrderingDuhamelIntegral : ℚ → ℚ → ℚ → ℚ
twoOrderingDuhamelIntegral x h k =
  oneOrderingIntegratedTelescope (x * h * k)
  + oneOrderingIntegratedTelescope (x * k * h)

twoOrderingDuhamelIntegralExact : ∀ x h k →
  twoOrderingDuhamelIntegral x h k ≡ x * h * k
twoOrderingDuhamelIntegralExact = ℚRing.solve-∀

pointwiseCoefficientSum : ℚ → ℚ → ℚ
pointwiseCoefficientSum r s =
  (one - s) + ((s - r) + r)

pointwiseCoefficientSumExact : ∀ r s →
  pointwiseCoefficientSum r s ≡ one
pointwiseCoefficientSumExact = ℚRing.solve-∀

oneOrderingIsHalfNotOne : ∀ scale →
  oneOrderingIntegratedTelescope scale
  ≡ orderedSimplexConstantIntegral scale
oneOrderingIsHalfNotOne = ℚRing.solve-∀

twoOrderingsAreOneNotTwo : ∀ scale →
  orderedSimplexConstantIntegral scale
  + orderedSimplexConstantIntegral scale
  ≡ scale
twoOrderingsAreOneNotTwo = ℚRing.solve-∀

orderedSimplexMeasureBookkeepingLevel : ProofLevel
orderedSimplexMeasureBookkeepingLevel = machineChecked

threeTelescopingIntegralsLevel : ProofLevel
threeTelescopingIntegralsLevel = machineChecked

twoOrderingNoFactorLossLevel : ProofLevel
twoOrderingNoFactorLossLevel = machineChecked
