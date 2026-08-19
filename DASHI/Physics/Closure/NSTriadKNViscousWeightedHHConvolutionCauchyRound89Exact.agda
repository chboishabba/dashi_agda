module DASHI.Physics.Closure.NSTriadKNViscousWeightedHHConvolutionCauchyRound89Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Title: finite Cauchy--Schwarz inequality.
-- DOI: not applicable to the nineteenth-century result.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Terence Tao.
-- Title: "Finite Time Blowup for an Averaged Three-Dimensional
-- Navier--Stokes Equation".
-- DOI: 10.1090/jams/838.
--
-- ROUND89 / DIRECT DISSIPATION CONTROL OF THE WEIGHTED HH CONVOLUTION
--
-- After the exact gradient-tensor symbol identity, the factor p dot q is not
-- estimated as an external dyadic coefficient.  For a fixed output k, the
-- relevant absolute convolution has the form
--
--     sum_{p+q=k} a_p b_q,
--
-- where a_p and b_q are derivative-weighted input magnitudes.  Finite
-- Cauchy--Schwarz gives
--
--     (sum a_p b_q)^2 <= (sum a_p^2)(sum b_q^2).
--
-- If both derivative masses are submasses of one high-frequency dissipation
-- budget D_high, then
--
--     (sum a_p b_q)^2 <= D_high^2.
--
-- Crucially there is NO shell-gap coefficient in this theorem.  The two high
-- derivatives have been absorbed into the dissipation masses before any
-- absolute-value majorization.  This is the finite analytic core replacing
-- the falsified Round88 strategy that paid |p dot q| ~ 4^d externally.
--
-- The remaining physical weld is to instantiate the Pair list with the
-- derivative-weighted magnitudes of the literal resonant Fourier fibre and to
-- prove its left/right norm sums are submasses of the literal D_high.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record DerivativeWeightedHHConvolutionBudget : Set where
  constructor derivative-weighted-hh-convolution-budget
  field
    derivativePairs : List L2.Pair
    highDissipation : ℚ
    highDissipationNonnegative : 0ℚ ≤ highDissipation
    leftDerivativeMassBelowDissipation :
      L2.leftNormSquared derivativePairs ≤ highDissipation
    rightDerivativeMassBelowDissipation :
      L2.rightNormSquared derivativePairs ≤ highDissipation

open DerivativeWeightedHHConvolutionBudget public

weightedHHConvolution : DerivativeWeightedHHConvolutionBudget → ℚ
weightedHHConvolution budget = L2.pairDot (derivativePairs budget)

weightedHHConvolutionSquare : DerivativeWeightedHHConvolutionBudget → ℚ
weightedHHConvolutionSquare budget =
  L2.square (weightedHHConvolution budget)

weightedHHConvolutionSquareBelowDerivativeMassProduct :
  (budget : DerivativeWeightedHHConvolutionBudget) →
  weightedHHConvolutionSquare budget
  ≤ L2.leftNormSquared (derivativePairs budget)
      * L2.rightNormSquared (derivativePairs budget)
weightedHHConvolutionSquareBelowDerivativeMassProduct budget =
  L2.finiteCauchySchwarzSquared (derivativePairs budget)

weightedHHConvolutionSquareBelowDissipationSquared :
  (budget : DerivativeWeightedHHConvolutionBudget) →
  weightedHHConvolutionSquare budget
  ≤ highDissipation budget * highDissipation budget
weightedHHConvolutionSquareBelowDissipationSquared budget =
  let
    left = L2.leftNormSquared (derivativePairs budget)
    right = L2.rightNormSquared (derivativePairs budget)
    D = highDissipation budget

    leftNonnegative : 0ℚ ≤ left
    leftNonnegative = L2.leftNormSquaredNonnegative (derivativePairs budget)

    rightNonnegative : 0ℚ ≤ right
    rightNonnegative = L2.rightNormSquaredNonnegative (derivativePairs budget)

    firstScale : left * right ≤ D * right
    firstScale =
      let instance rightNN = nonNegative rightNonnegative
      in ℚP.*-monoʳ-≤-nonNeg right
        (leftDerivativeMassBelowDissipation budget)

    secondScale : D * right ≤ D * D
    secondScale =
      let instance dNN = nonNegative (highDissipationNonnegative budget)
      in ℚP.*-monoˡ-≤-nonNeg D
        (rightDerivativeMassBelowDissipation budget)
  in
  ℚP.≤-trans
    (weightedHHConvolutionSquareBelowDerivativeMassProduct budget)
    (ℚP.≤-trans firstScale secondScale)

round89WeightedHHConvolutionHasNoGapCoefficient : Bool
round89WeightedHHConvolutionHasNoGapCoefficient = true

round89WeightedHHConvolutionControlledByDissipationSquared : Bool
round89WeightedHHConvolutionControlledByDissipationSquared = true

round89LiteralFourierDerivativePairListConstructed : Bool
round89LiteralFourierDerivativePairListConstructed = false

round89WeightedHHConvolutionHasNoGapCoefficientIsTrue :
  round89WeightedHHConvolutionHasNoGapCoefficient ≡ true
round89WeightedHHConvolutionHasNoGapCoefficientIsTrue = refl

round89WeightedHHConvolutionControlledByDissipationSquaredIsTrue :
  round89WeightedHHConvolutionControlledByDissipationSquared ≡ true
round89WeightedHHConvolutionControlledByDissipationSquaredIsTrue = refl
