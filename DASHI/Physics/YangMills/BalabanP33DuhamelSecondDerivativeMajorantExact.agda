module DASHI.Physics.YangMills.BalabanP33DuhamelSecondDerivativeMajorantExact where

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
-- In the ordered-simplex formula for D^2 exp_X[H,K], one integrand is
--
--   E_(1-s) H E_(s-r) K E_r,   0 <= r <= s <= 1.
--
-- Subtracting HK and telescoping the three exponential factors gives scalar
-- norm coefficients
--
--   (1-s)||X|| + (s-r)||X|| + r||X|| = ||X||.
--
-- The simplex has area 1/2 and there are two H/K orderings, so the sharp
-- scalar majorant is ||X||||H||||K||, not 6||X||||H||||K||.  The physical
-- Bochner/Duhamel identification remains a separate analytic producer, but all
-- noncommutative telescope coefficients and P33 budget arithmetic are closed
-- here exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

oneMinus : ℚ → ℚ
oneMinus value = (+ 1 / 1) - value

threeExponentialDefectMajorant :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
threeExponentialDefectMajorant x h k r s =
  ((oneMinus s) * x) * h * k
  + (h * ((s - r) * x) * k
  + h * k * (r * x))

simplexSegmentCoefficientsSumToOne : ∀ r s →
  oneMinus s + ((s - r) + r) ≡ (+ 1 / 1)
simplexSegmentCoefficientsSumToOne = ℚRing.solve-∀

threeExponentialDefectMajorantExact : ∀ x h k r s →
  threeExponentialDefectMajorant x h k r s
  ≡ x * h * k
threeExponentialDefectMajorantExact = ℚRing.solve-∀

orderedSimplexArea : ℚ
orderedSimplexArea = + 1 / 2

twoOrderedSimplexAreas : ℚ
twoOrderedSimplexAreas = orderedSimplexArea + orderedSimplexArea

twoOrderedSimplexAreasAreOne :
  twoOrderedSimplexAreas ≡ (+ 1 / 1)
twoOrderedSimplexAreasAreOne = ℚRing.solve []

secondDerivativeDuhamelMajorant : ℚ → ℚ → ℚ → ℚ
secondDerivativeDuhamelMajorant x h k =
  orderedSimplexArea * (x * h * k)
  + orderedSimplexArea * (x * k * h)

secondDerivativeDuhamelMajorantExact : ∀ x h k →
  secondDerivativeDuhamelMajorant x h k ≡ x * h * k
secondDerivativeDuhamelMajorantExact = ℚRing.solve-∀

p33Radius localSecondChartRadius : ℚ
p33Radius = + 1 / 8192
localSecondChartRadius = p33Radius * (+ 1 / 96)

sharpSecondChartAllocation configuredSecondChartAllocation : ℚ
sharpSecondChartAllocation = localSecondChartRadius
configuredSecondChartAllocation = p33Radius * (+ 1 / 16)

sharpSecondChartAllocationExact :
  sharpSecondChartAllocation ≡ p33Radius * (+ 1 / 96)
sharpSecondChartAllocationExact = ℚRing.solve []

configuredSixLipschitzFitsExactly :
  (+ 6 / 1) * localSecondChartRadius
  ≡ configuredSecondChartAllocation
configuredSixLipschitzFitsExactly = ℚRing.solve []

sharpMajorantSlack : ℚ
sharpMajorantSlack = p33Radius * (+ 5 / 96)

sharpMajorantPlusSlackIsConfiguredAllocation :
  sharpSecondChartAllocation + sharpMajorantSlack
  ≡ configuredSecondChartAllocation
sharpMajorantPlusSlackIsConfiguredAllocation = ℚRing.solve []

fourDiagonalSharpBudget : ℚ
fourDiagonalSharpBudget = (+ 4 / 1) * sharpSecondChartAllocation

fourDiagonalSharpBudgetExact :
  fourDiagonalSharpBudget ≡ p33Radius * (+ 1 / 24)
fourDiagonalSharpBudgetExact = ℚRing.solve []

simplexDuhamelCoefficientLevel : ProofLevel
simplexDuhamelCoefficientLevel = machineChecked

sharpSecondDerivativeMajorantArithmeticLevel : ProofLevel
sharpSecondDerivativeMajorantArithmeticLevel = machineChecked

physicalDuhamelBochnerIdentificationLevel : ProofLevel
physicalDuhamelBochnerIdentificationLevel = conditional
