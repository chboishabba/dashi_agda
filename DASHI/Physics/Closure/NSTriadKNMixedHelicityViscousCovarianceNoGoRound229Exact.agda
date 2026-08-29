module DASHI.Physics.Closure.NSTriadKNMixedHelicityViscousCovarianceNoGoRound229Exact where

------------------------------------------------------------------------
-- ROUND229 / VISCOUS LOWER BOUNDS DO NOT SURVIVE COHERENT SUMMATION
--
-- Round218 proves for every resonant incidence p+q=k
--
--   |k|^2 <= 2 (|p|^2 + |q|^2).
--
-- It is tempting to infer that the mixed-helicity fixed-output sum
--
--   M_k = sum_{p+q=k} c_pq
--
-- inherits coherent damping at rate at least nu |k|^2 / 2 from the cellwise
-- rates nu(|p|^2+|q|^2).  That inference is false without a covariance theorem.
--
-- After writing each rate as common + excess, the norm tangent contains
--
--   Re < sum c_i , sum excess_i c_i >.
--
-- Nonnegative excess_i do NOT force this pairing to be nonnegative.  The
-- exact rational scalar witness below already gives an adverse sign:
--
--   c1 = 1, c2 = -2, e1 = 2, e2 = 0,
--
--   (c1+c2)(e1*c1+e2*c2) = (-1)(2) = -2 < 0.
--
-- Thus cellwise viscosity cannot by itself close the Round228 spacetime leaf;
-- signed/coherent structure is still required after summation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; _<_)
open import Data.Rational.Tactic.RingSolver using (solve)

one two : ℚ
one = 1ℚ
two = 1ℚ + 1ℚ

c1 c2 e1 e2 : ℚ
c1 = one
c2 = 0ℚ - two
e1 = two
e2 = 0ℚ

coherentCellSum : ℚ
coherentCellSum = c1 + c2

excessWeightedSum : ℚ
excessWeightedSum = e1 * c1 + e2 * c2

coherentExcessPairing : ℚ
coherentExcessPairing = coherentCellSum * excessWeightedSum

excessWeightsNonnegative : (0ℚ ≤ e1) × (0ℚ ≤ e2)
excessWeightsNonnegative = refl , refl

coherentCellSumIsMinusOne : coherentCellSum ≡ 0ℚ - one
coherentCellSumIsMinusOne = solve []

excessWeightedSumIsTwo : excessWeightedSum ≡ two
excessWeightedSumIsTwo = solve []

coherentExcessPairingIsMinusTwo : coherentExcessPairing ≡ 0ℚ - two
coherentExcessPairingIsMinusTwo = solve []

coherentExcessPairingNegative : coherentExcessPairing < 0ℚ
coherentExcessPairingNegative = refl

round229CellwiseViscousLowerBoundImpliesCoherentDamping : Bool
round229CellwiseViscousLowerBoundImpliesCoherentDamping = false

round229WeightedCoherentCovarianceCanBeAdverse : Bool
round229WeightedCoherentCovarianceCanBeAdverse = true

round229DynamicHeatRouteStillNeedsSignedCovariance : Bool
round229DynamicHeatRouteStillNeedsSignedCovariance = true

round229PackageAClosed : Bool
round229PackageAClosed = false

round229ClayPromotion : Bool
round229ClayPromotion = false

round229CellwiseViscousLowerBoundImpliesCoherentDampingIsFalse :
  round229CellwiseViscousLowerBoundImpliesCoherentDamping ≡ false
round229CellwiseViscousLowerBoundImpliesCoherentDampingIsFalse = refl

round229WeightedCoherentCovarianceCanBeAdverseIsTrue :
  round229WeightedCoherentCovarianceCanBeAdverse ≡ true
round229WeightedCoherentCovarianceCanBeAdverseIsTrue = refl

round229DynamicHeatRouteStillNeedsSignedCovarianceIsTrue :
  round229DynamicHeatRouteStillNeedsSignedCovariance ≡ true
round229DynamicHeatRouteStillNeedsSignedCovarianceIsTrue = refl

round229PackageAClosedIsFalse : round229PackageAClosed ≡ false
round229PackageAClosedIsFalse = refl

round229ClayPromotionIsFalse : round229ClayPromotion ≡ false
round229ClayPromotionIsFalse = refl
