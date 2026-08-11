module DASHI.Physics.Closure.NSTriadKNHHGoodSquaredBudgetRound39Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 38 proved the physical good-pair estimate
--
--   |stretch|^2 <= delta * a^2 * b^4.
--
-- The informal budget scaling is eta_HHg ~ C_PV sqrt(delta).  Rather than
-- introduce a square-root primitive merely to state that fact, this module
-- proves the exact division-free squared criterion needed by the rational
-- owner optimizer:
--
--   C_PV^2 * delta <= eta_HHg^2
--
-- implies
--
--   C_PV^2 * |stretch|^2
--      <= eta_HHg^2 * a^2 * b^4.
--
-- Hence the classifier threshold can already be solved against an eventual
-- rigorous PV constant using exact rational arithmetic.  Extracting an
-- unsquared L1/PV owner estimate still belongs to the physical A3/A4 theorem;
-- no square-root monotonicity or continuum norm theorem is fabricated here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNVortexStretchingGeometricFactorRound37Exact as Stretch
import DASHI.Physics.Closure.NSTriadKNHHGoodPhysicalThresholdStretchingRound38Exact as Good

square : ℚ → ℚ
square value = value * value

squareNonnegative : ∀ value → 0ℚ ≤ square value
squareNonnegative = L2.squareNonnegative

record HHGoodSquaredBudget
    (parameter : Threshold.PositiveThreshold) : Set where
  constructor hh-good-squared-budget
  field
    pvConstant ownerEta : ℚ
    pvConstantNonnegative : 0ℚ ≤ pvConstant
    ownerEtaNonnegative : 0ℚ ≤ ownerEta
    squaredThresholdFitsReserve :
      square pvConstant * Threshold.threshold parameter
      ≤ square ownerEta

open HHGoodSquaredBudget public

thresholdWeightNonnegative :
  ∀ parameter physical →
  0ℚ ≤ Threshold.threshold parameter * Good.amplitudeQuarticWeight physical
thresholdWeightNonnegative parameter physical =
  L2.nonnegativeProductMonotone
    ℚP.≤-refl ℚP.≤-refl
    (Threshold.thresholdNonnegative parameter)
    (Good.amplitudeQuarticWeightNonnegative physical)
    (Threshold.thresholdNonnegative parameter)
    (Good.amplitudeQuarticWeightNonnegative physical)

squaredHHGoodBudgetAbsorption :
  ∀ theta parameter
    (budget : HHGoodSquaredBudget parameter)
    (good : Good.PhysicalHHGoodPair parameter) →
  V.normSquared theta ≡ 1ℚ →
  square (pvConstant budget)
    * L2.square
        (Stretch.stretchingScalar theta
          (Good.sourceVector (Good.pair good))
          (Good.targetVector (Good.pair good)))
  ≤
  square (ownerEta budget)
    * Good.amplitudeQuarticWeight (Good.pair good)
squaredHHGoodBudgetAbsorption theta parameter budget good thetaUnit =
  let
    physical = Good.pair good
    stretchSquare =
      L2.square
        (Stretch.stretchingScalar theta
          (Good.sourceVector physical)
          (Good.targetVector physical))
    thresholdWeight =
      Threshold.threshold parameter
        * Good.amplitudeQuarticWeight physical

    local : stretchSquare ≤ thresholdWeight
    local = Good.goodPhysicalStretchingThresholdBound
      theta parameter good thetaUnit

    first :
      square (pvConstant budget) * stretchSquare
      ≤ square (pvConstant budget) * thresholdWeight
    first =
      L2.nonnegativeProductMonotone
        (squareNonnegative (pvConstant budget))
        (squareNonnegative
          (Stretch.stretchingScalar theta
            (Good.sourceVector physical)
            (Good.targetVector physical)))
        (squareNonnegative (pvConstant budget))
        (thresholdWeightNonnegative parameter physical)
        ℚP.≤-refl
        local

    regroup :
      square (pvConstant budget) * thresholdWeight
      ≡
      (square (pvConstant budget) * Threshold.threshold parameter)
        * Good.amplitudeQuarticWeight physical
    regroup = solve
      ( pvConstant budget
      ∷ Threshold.threshold parameter
      ∷ Good.amplitudeQuarticWeight physical
      ∷ [])

    reserveTimesWeight :
      (square (pvConstant budget) * Threshold.threshold parameter)
        * Good.amplitudeQuarticWeight physical
      ≤
      square (ownerEta budget)
        * Good.amplitudeQuarticWeight physical
    reserveTimesWeight =
      L2.nonnegativeProductMonotone
        (L2.nonnegativeProductMonotone
          (squareNonnegative (pvConstant budget))
          (Threshold.thresholdNonnegative parameter)
          (squareNonnegative (pvConstant budget))
          (Threshold.thresholdNonnegative parameter)
          ℚP.≤-refl ℚP.≤-refl)
        (Good.amplitudeQuarticWeightNonnegative physical)
        (squareNonnegative (ownerEta budget))
        (Good.amplitudeQuarticWeightNonnegative physical)
        (squaredThresholdFitsReserve budget)
        ℚP.≤-refl
  in
  ℚP.≤-trans first
    (subst
      (λ middle →
        middle
        ≤ square (ownerEta budget)
            * Good.amplitudeQuarticWeight physical)
      (symmetry regroup)
      reserveTimesWeight)
  where
  symmetry : ∀ {a b : ℚ} → a ≡ b → b ≡ a
  symmetry refl = refl

hhGoodSquaredBudgetCriterionClosed : Bool
hhGoodSquaredBudgetCriterionClosed = true

physicalUnsquaredPVHHGoodOwnerAbsorptionConstructed : Bool
physicalUnsquaredPVHHGoodOwnerAbsorptionConstructed = false

hhGoodSquaredBudgetCriterionClosedIsTrue :
  hhGoodSquaredBudgetCriterionClosed ≡ true
hhGoodSquaredBudgetCriterionClosedIsTrue = refl
