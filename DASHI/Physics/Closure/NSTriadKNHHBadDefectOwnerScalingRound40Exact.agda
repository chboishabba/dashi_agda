module DASHI.Physics.Closure.NSTriadKNHHBadDefectOwnerScalingRound40Exact where

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
-- Turn the Round-40 bad-defect estimate into the exact owner scaling suggested
-- by the good/bad threshold synthesis.  If
--
--   delta * Gain_bad <= DefectCharge
--   DefectCharge <= B * Dissipation,
--
-- and delta is a `PositiveThreshold` with exact inverse, then
--
--   Gain_bad <= delta^{-1} * B * Dissipation.
--
-- This is proved by multiplying the first inequality by the exact positive
-- inverse and normalising, not by postulating a division operation.  Hence the
-- B/delta branch of the symbolic threshold optimizer is now an exact
-- consequence of a single physical weighted-directional-defect owner rate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record BadDefectOwnerRate
    (parameter : Threshold.PositiveThreshold) : Set where
  field
    badGain defectCharge dissipation defectRate : ℚ
    badGainNonnegative : 0ℚ ≤ badGain
    defectChargeNonnegative : 0ℚ ≤ defectCharge
    dissipationNonnegative : 0ℚ ≤ dissipation
    defectRateNonnegative : 0ℚ ≤ defectRate

    thresholdTimesGainBelowDefect :
      Threshold.threshold parameter * badGain ≤ defectCharge

    defectBelowRateTimesDissipation :
      defectCharge ≤ defectRate * dissipation

open BadDefectOwnerRate public

inverseThresholdNonnegative :
  (parameter : Threshold.PositiveThreshold) →
  0ℚ ≤ Threshold.thresholdInverse parameter
inverseThresholdNonnegative = Threshold.thresholdInverseNonnegative

badGainBelowInverseThresholdDefect :
  ∀ {parameter}
    (rate : BadDefectOwnerRate parameter) →
  badGain rate
  ≤ Threshold.thresholdInverse parameter * defectCharge rate
badGainBelowInverseThresholdDefect {parameter} rate =
  let
    scaled :
      Threshold.thresholdInverse parameter
        * (Threshold.threshold parameter * badGain rate)
      ≤ Threshold.thresholdInverse parameter * defectCharge rate
    scaled =
      let instance invNN = nonNegative (inverseThresholdNonnegative parameter)
      in ℚP.*-monoˡ-≤-nonNeg
        (Threshold.thresholdInverse parameter)
        (thresholdTimesGainBelowDefect rate)

    leftMeaning :
      Threshold.thresholdInverse parameter
        * (Threshold.threshold parameter * badGain rate)
      ≡ badGain rate
    leftMeaning =
      trans
        (solve
          ( Threshold.thresholdInverse parameter
          ∷ Threshold.threshold parameter
          ∷ badGain rate
          ∷ []))
        (subst
          (λ product → product * badGain rate ≡ badGain rate)
          (Threshold.inverseMeaning parameter)
          (solve (badGain rate ∷ [])))
  in
  subst
    (λ lower → lower ≤ Threshold.thresholdInverse parameter * defectCharge rate)
    leftMeaning
    scaled

badGainBelowBOverDeltaDissipation :
  ∀ {parameter}
    (rate : BadDefectOwnerRate parameter) →
  badGain rate
  ≤ Threshold.thresholdInverse parameter
      * defectRate rate * dissipation rate
badGainBelowBOverDeltaDissipation {parameter} rate =
  let
    first = badGainBelowInverseThresholdDefect rate

    scaledDefect :
      Threshold.thresholdInverse parameter * defectCharge rate
      ≤ Threshold.thresholdInverse parameter
          * (defectRate rate * dissipation rate)
    scaledDefect =
      let instance invNN = nonNegative (inverseThresholdNonnegative parameter)
      in ℚP.*-monoˡ-≤-nonNeg
        (Threshold.thresholdInverse parameter)
        (defectBelowRateTimesDissipation rate)

    regroup :
      Threshold.thresholdInverse parameter
        * (defectRate rate * dissipation rate)
      ≡ Threshold.thresholdInverse parameter
          * defectRate rate * dissipation rate
    regroup = solve
      ( Threshold.thresholdInverse parameter
      ∷ defectRate rate
      ∷ dissipation rate
      ∷ [])
  in
  ℚP.≤-trans first
    (subst
      (λ upper →
        Threshold.thresholdInverse parameter * defectCharge rate ≤ upper)
      regroup
      scaledDefect)

hhBadDefectOwnerScalingClosed : Bool
hhBadDefectOwnerScalingClosed = true

physicalTimeIntegratedDefectOwnerRateConstructed : Bool
physicalTimeIntegratedDefectOwnerRateConstructed = false

hhBadDefectOwnerScalingClosedIsTrue :
  hhBadDefectOwnerScalingClosed ≡ true
hhBadDefectOwnerScalingClosedIsTrue = refl
