module DASHI.Physics.Closure.NSTriadKNHHDirectionalDefectSharedBudgetRound41Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- Indiana University Mathematics Journal 42 (1993), 775--789.
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
-- Round 40 showed that HH-good depletion and HH-bad occupation are two uses
-- of the same energy-weighted directional defect.  This file makes the next
-- proposed step exact: one physical time-integrated bound on
--
--   D_dir = sum E_i Theta_i
--
-- can feed both sides of the HH split.
--
-- If
--
--   D_dir <= alpha D + A + B X,
--
-- then the existing weighted Markov theorem immediately gives
--
--   delta E_bad <= alpha D + A + B X.
--
-- Any HH-good quantity whose square is bounded by
--
--   C delta D_dir
--
-- is simultaneously bounded by C delta times the same owner-shaped right
-- hand side.  No second defect evolution, no differentiated classifier, and
-- no independently selected bad occupation measure is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHUnifiedDirectionalDefectRound40Exact as Defect

record PhysicalDirectionalDefectBudget
    (environment : Owner.TaxEnvironment)
    (parameter : Threshold.PositiveThreshold) : Set where
  field
    badCells : List (Defect.PhysicalBadDirectionalEnergyCell parameter)
    eta dataRemainder criticalCoefficient : ℚ

    etaNonnegative : 0ℚ ≤ eta
    dataRemainderNonnegative : 0ℚ ≤ dataRemainder
    criticalCoefficientNonnegative : 0ℚ ≤ criticalCoefficient
    dissipationNonnegative : 0ℚ ≤ Owner.dissipation environment
    integralCriticalNonnegative : 0ℚ ≤ Owner.integralCritical environment

    timeIntegratedDirectionalDefectBound :
      Defect.weightedDirectionalDefectMass badCells
      ≤ eta * Owner.dissipation environment
        + dataRemainder
        + criticalCoefficient * Owner.integralCritical environment

open PhysicalDirectionalDefectBudget public

defectBudgetRight :
  ∀ {environment parameter} →
  PhysicalDirectionalDefectBudget environment parameter → ℚ
defectBudgetRight {environment} budget =
  eta budget * Owner.dissipation environment
  + dataRemainder budget
  + criticalCoefficient budget * Owner.integralCritical environment

thresholdBadEnergyBelowSharedBudget :
  ∀ {environment parameter}
    (budget : PhysicalDirectionalDefectBudget environment parameter) →
  Threshold.threshold parameter
    * Defect.badEnergyMass (badCells budget)
  ≤ defectBudgetRight budget
thresholdBadEnergyBelowSharedBudget budget =
  ℚP.≤-trans
    (Defect.thresholdTimesBadEnergyBelowDirectionalDefect (badCells budget))
    (timeIntegratedDirectionalDefectBound budget)

record HHGoodUseOfDirectionalDefect
    {environment : Owner.TaxEnvironment}
    {parameter : Threshold.PositiveThreshold}
    (budget : PhysicalDirectionalDefectBudget environment parameter) : Set where
  field
    goodProductionSquare coefficient : ℚ
    coefficientNonnegative : 0ℚ ≤ coefficient
    goodProductionSquareNonnegative : 0ℚ ≤ goodProductionSquare
    goodSquareBelowDefect :
      goodProductionSquare
      ≤ coefficient * Threshold.threshold parameter
          * Defect.weightedDirectionalDefectMass (badCells budget)

open HHGoodUseOfDirectionalDefect public

goodSquareBelowScaledSharedBudget :
  ∀ {environment parameter}
    {budget : PhysicalDirectionalDefectBudget environment parameter} →
  (good : HHGoodUseOfDirectionalDefect budget) →
  goodProductionSquare good
  ≤ coefficient good * Threshold.threshold parameter
      * defectBudgetRight budget
goodSquareBelowScaledSharedBudget {parameter = parameter} {budget} good =
  let
    scale = coefficient good * Threshold.threshold parameter
    scaleNN : 0ℚ ≤ scale
    scaleNN =
      let
        instance
          coefficientNNI = nonNegative (coefficientNonnegative good)
          thresholdNNI = nonNegative (Threshold.thresholdNonnegative parameter)
          productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
            (coefficient good) (Threshold.threshold parameter)
      in
      ℚP.nonNegative⁻¹ scale

    scaledDefect :
      scale * Defect.weightedDirectionalDefectMass (badCells budget)
      ≤ scale * defectBudgetRight budget
    scaledDefect =
      let instance scaleNNI = nonNegative scaleNN
      in ℚP.*-monoˡ-≤-nonNeg scale
        (timeIntegratedDirectionalDefectBound budget)

    lowerMeaning :
      coefficient good * Threshold.threshold parameter
        * Defect.weightedDirectionalDefectMass (badCells budget)
      ≡ scale * Defect.weightedDirectionalDefectMass (badCells budget)
    lowerMeaning = refl

    first :
      goodProductionSquare good
      ≤ scale * Defect.weightedDirectionalDefectMass (badCells budget)
    first = subst
      (λ upper → goodProductionSquare good ≤ upper)
      lowerMeaning
      (goodSquareBelowDefect good)
  in
  ℚP.≤-trans first scaledDefect

sharedDirectionalDefectBudgetClosed : Bool
sharedDirectionalDefectBudgetClosed = true

physicalTimeIntegratedDirectionalDefectBudgetConstructed : Bool
physicalTimeIntegratedDirectionalDefectBudgetConstructed = false

sharedDirectionalDefectBudgetClosedIsTrue :
  sharedDirectionalDefectBudgetClosed ≡ true
sharedDirectionalDefectBudgetClosedIsTrue = refl
