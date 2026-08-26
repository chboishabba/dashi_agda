module DASHI.Core.FiniteBranchingCriticalityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Theodore E. Harris,
-- "The Theory of Branching Processes", Springer, 1963.
-- DOI: 10.1007/978-3-642-51866-9.
--
-- E. Seneta,
-- "Non-negative Matrices and Markov Chains", 2nd ed., Springer, 1981.
-- DOI: 10.1007/0-387-32792-4.
--
-- SOURCE SCOPE
--
-- Harris is the classical branching-process source for the subcritical /
-- critical / supercritical distinction based on mean reproduction.  Seneta is
-- included for the Perron--Frobenius/non-negative-matrix background motivating
-- the multitype extension discussed in the supplied DASHI notes.
--
-- DASHI CONTRIBUTION
--
-- This file is deliberately finite and exact.  It represents an availability
-- p/d by natural-number numerator/denominator, computes the scaled mean
-- offspring q*p/d, and classifies that rational quantity by comparing q*p to d.
-- It also computes the product-model numerator for several independent axes.
--
-- It does NOT prove stochastic independence, extinction probabilities, a
-- probability measure, or a Perron--Frobenius spectral-radius theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

------------------------------------------------------------------------
-- Executable finite comparison.
------------------------------------------------------------------------

data BranchingRegime : Set where
  subcritical critical supercritical : BranchingRegime

classifyScaled : Nat → Nat → BranchingRegime
classifyScaled zero zero = critical
classifyScaled zero (suc denominator) = subcritical
classifyScaled (suc numerator) zero = supercritical
classifyScaled (suc numerator) (suc denominator) =
  classifyScaled numerator denominator

pow : Nat → Nat → Nat
pow base zero = 1
pow base (suc exponent) = base * pow base exponent

------------------------------------------------------------------------
-- Homogeneous one-type branching arithmetic.
--
-- If a node has `arity` possible descendants and each branch is assigned the
-- same scaled availability p/d, the mean-offspring ratio is (arity*p)/d.
------------------------------------------------------------------------

offspringNumerator : Nat → Nat → Nat
offspringNumerator arity availabilityNumerator =
  arity * availabilityNumerator

singleAxisRegime : Nat → Nat → Nat → BranchingRegime
singleAxisRegime arity availabilityNumerator availabilityDenominator =
  classifyScaled
    (offspringNumerator arity availabilityNumerator)
    availabilityDenominator

binaryHalfIsCritical : singleAxisRegime 2 1 2 ≡ critical
binaryHalfIsCritical = refl

ternaryThirdIsCritical : singleAxisRegime 3 1 3 ≡ critical
ternaryThirdIsCritical = refl

quaternaryQuarterIsCritical : singleAxisRegime 4 1 4 ≡ critical
quaternaryQuarterIsCritical = refl

ternaryFiveEighteenthsIsSubcritical :
  singleAxisRegime 3 5 18 ≡ subcritical
ternaryFiveEighteenthsIsSubcritical = refl

ternaryFiveEighteenthsOffspringNumeratorIsFifteen :
  offspringNumerator 3 5 ≡ 15
ternaryFiveEighteenthsOffspringNumeratorIsFifteen = refl

------------------------------------------------------------------------
-- Independent-axis product model.
--
-- For `axes` simultaneous coordinates, the unnormalised accessible-cell
-- numerator is (arity * p)^axes and its denominator is d^axes.  This is the
-- exact arithmetic behind the supplied toy formula 27 p^3 = (3p)^3 when
-- arity=3 and axes=3.
------------------------------------------------------------------------

jointAccessibleNumerator : Nat → Nat → Nat → Nat
jointAccessibleNumerator arity axes availabilityNumerator =
  pow (arity * availabilityNumerator) axes

jointAccessibleDenominator : Nat → Nat → Nat
jointAccessibleDenominator axes availabilityDenominator =
  pow availabilityDenominator axes

threeTernaryAxesCellCount : jointAccessibleNumerator 3 3 1 ≡ 27
threeTernaryAxesCellCount = refl

threeAxisNinetyPercentNumerator :
  jointAccessibleNumerator 3 3 9 ≡ 19683
threeAxisNinetyPercentNumerator = refl

threeAxisNinetyPercentDenominator :
  jointAccessibleDenominator 3 10 ≡ 1000
threeAxisNinetyPercentDenominator = refl

threeAxisFiveEighteenthsNumerator :
  jointAccessibleNumerator 3 3 5 ≡ 3375
threeAxisFiveEighteenthsNumerator = refl

threeAxisFiveEighteenthsDenominator :
  jointAccessibleDenominator 3 18 ≡ 5832
threeAxisFiveEighteenthsDenominator = refl

------------------------------------------------------------------------
-- Per-axis 10% multiplicative gain.
--
-- Scaling one axis by 11/10 and applying the same factor independently over
-- three simultaneous axes gives 11^3 / 10^3 = 1331/1000.
------------------------------------------------------------------------

threeAxisTenPercentGainNumerator : pow 11 3 ≡ 1331
threeAxisTenPercentGainNumerator = refl

threeAxisTenPercentGainDenominator : pow 10 3 ≡ 1000
threeAxisTenPercentGainDenominator = refl

------------------------------------------------------------------------
-- Exact affine fixed-point cross-equation from the supplied historical note.
--
-- x = 1/4 + x/10.
-- If x = n/d, clearing denominators gives 40n = 10d + 4n.
-- The supplied fixed point 5/18 satisfies that equation exactly.
------------------------------------------------------------------------

affineQuarterTenthFixedPointEquation : Nat → Nat → Set
affineQuarterTenthFixedPointEquation numerator denominator =
  40 * numerator ≡ 10 * denominator + 4 * numerator

fiveEighteenthsSolvesAffineQuarterTenth :
  affineQuarterTenthFixedPointEquation 5 18
fiveEighteenthsSolvesAffineQuarterTenth = refl

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record FiniteBranchingCriticalityBoundary : Set where
  constructor finite-branching-criticality-boundary
  field
    homogeneousAvailabilityIsEmpiricalIndependenceClaim : Bool
    homogeneousAvailabilityIsEmpiricalIndependenceClaimIsFalse :
      homogeneousAvailabilityIsEmpiricalIndependenceClaim ≡ false
    scaledCountIsFullProbabilityMeasure : Bool
    scaledCountIsFullProbabilityMeasureIsFalse :
      scaledCountIsFullProbabilityMeasure ≡ false
    multitypePerronFrobeniusTheoremConstructedHere : Bool
    multitypePerronFrobeniusTheoremConstructedHereIsFalse :
      multitypePerronFrobeniusTheoremConstructedHere ≡ false

canonicalFiniteBranchingCriticalityBoundary :
  FiniteBranchingCriticalityBoundary
canonicalFiniteBranchingCriticalityBoundary =
  finite-branching-criticality-boundary
    false refl
    false refl
    false refl
