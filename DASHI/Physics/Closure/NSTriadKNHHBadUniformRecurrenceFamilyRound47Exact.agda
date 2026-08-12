module DASHI.Physics.Closure.NSTriadKNHHBadUniformRecurrenceFamilyRound47Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- This is the exact Round-47 criterion for a genuine threshold-independent
-- normalized HH-bad ceiling.  A single set of physical recurrence data
--
--   M, alpha, beta
--
-- shared by every admissible threshold is sufficient if
--
--   B_0(delta) <= delta M,
--   B_(q+1)(delta) <= (alpha/2) B_q(delta)
--                    + delta 2^(-(q+1)) beta,
--   alpha < 1,
--   beta <= (1-alpha) M.
--
-- The theorem then derives
--
--   delta^(-1) 2^q B_q(delta) <= M
--
-- for every threshold and shell.  This isolates the three genuinely physical
-- failure points: base shell, contraction, or forcing.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as Scale
import DASHI.Physics.Closure.NSTriadKNHHBadDefectRecurrenceNormalizationRound46Exact as Defect
import DASHI.Physics.Closure.NSTriadKNHHBadVariableProfileRecurrenceRound46Exact as Recurrence

record ThresholdUniformDefectRecurrenceFamily : Set where
  field
    defectRate : Threshold.PositiveThreshold → Nat → ℚ
    defectRateNonnegative : ∀ parameter q → 0ℚ ≤ defectRate parameter q

    ceiling alpha beta : ℚ
    ceilingNonnegative : 0ℚ ≤ ceiling
    alphaNonnegative : 0ℚ ≤ alpha
    betaNonnegative : 0ℚ ≤ beta
    alphaStrict : alpha < 1ℚ

    baseLinearInThreshold : ∀ parameter →
      defectRate parameter zero
      ≤ Threshold.threshold parameter * ceiling

    oneShellTransfer : ∀ parameter q →
      defectRate parameter (Agda.Builtin.Nat.suc q)
      ≤ alpha * Sharp.half * defectRate parameter q
        + Threshold.threshold parameter
          * Sharp.inverseDyadicScale (Agda.Builtin.Nat.suc q) * beta

    forcingFitsCeiling : beta ≤ (1ℚ - alpha) * ceiling

open ThresholdUniformDefectRecurrenceFamily public

recurrenceAtThreshold :
  ThresholdUniformDefectRecurrenceFamily →
  Threshold.PositiveThreshold →
  Defect.PhysicalDefectShellRecurrence
recurrenceAtThreshold family parameter = record
  { defectRate = defectRate family parameter
  ; alpha = alpha family
  ; beta = beta family
  ; defectRateNonnegative = defectRateNonnegative family parameter
  ; alphaNonnegative = alphaNonnegative family
  ; betaNonnegative = betaNonnegative family
  ; oneShellDefectTransfer = oneShellTransfer family parameter
  }

normalizedBaseBelowCeiling :
  (family : ThresholdUniformDefectRecurrenceFamily) →
  (parameter : Threshold.PositiveThreshold) →
  Defect.normalizedDefectProfile (recurrenceAtThreshold family parameter) zero
  ≤ ceiling family
normalizedBaseBelowCeiling family parameter =
  let
    inverse = Threshold.thresholdInverse parameter
    delta = Threshold.threshold parameter
    base = defectRate family parameter zero
    M = ceiling family

    scaled : inverse * base ≤ inverse * (delta * M)
    scaled =
      let instance inverseNNI = nonNegative (Threshold.thresholdInverseNonnegative parameter)
      in ℚP.*-monoˡ-≤-nonNeg inverse (baseLinearInThreshold family parameter)

    leftMeaning :
      inverse * base
      ≡ Defect.normalizedDefectProfile
          (recurrenceAtThreshold family parameter) zero
    leftMeaning = solve (inverse ∷ base ∷ [])

    rightMeaning : inverse * (delta * M) ≡ M
    rightMeaning rewrite Threshold.inverseMeaning parameter =
      solve (M ∷ [])
  in
  subst
    (λ left → left ≤ M)
    leftMeaning
    (subst
      (λ right → inverse * base ≤ right)
      rightMeaning
      scaled)

profileNonnegative :
  (family : ThresholdUniformDefectRecurrenceFamily) →
  (parameter : Threshold.PositiveThreshold) →
  ∀ q →
  0ℚ ≤ Defect.normalizedDefectProfile
    (recurrenceAtThreshold family parameter) q
profileNonnegative family parameter q =
  let
    inverseNN = Threshold.thresholdInverseNonnegative parameter
    scaleNN = Scale.dyadicScaleNonnegative q
    defectNN = defectRateNonnegative family parameter q
    instance
      inverseNNI = nonNegative inverseNN
      scaleNNI = nonNegative scaleNN
      firstNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (Threshold.thresholdInverse parameter)
          (Sharp.dyadicScale q)
      defectNNI = nonNegative defectNN
      secondNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (Threshold.thresholdInverse parameter * Sharp.dyadicScale q)
          (defectRate family parameter q)
  in
  ℚP.nonNegative⁻¹
    (Defect.normalizedDefectProfile
      (recurrenceAtThreshold family parameter) q)

contractiveProfileAtThreshold :
  (family : ThresholdUniformDefectRecurrenceFamily) →
  (parameter : Threshold.PositiveThreshold) →
  Recurrence.VariableContractiveProfileRecurrence
contractiveProfileAtThreshold family parameter = record
  { profile = Defect.normalizedDefectProfile
      (recurrenceAtThreshold family parameter)
  ; alpha = λ _ → alpha family
  ; beta = λ _ → beta family
  ; alphaBar = alpha family
  ; ceiling = ceiling family
  ; profileNonnegative = profileNonnegative family parameter
  ; alphaNonnegative = λ _ → alphaNonnegative family
  ; betaNonnegative = λ _ → betaNonnegative family
  ; ceilingNonnegative = ceilingNonnegative family
  ; alphaBarNonnegative = alphaNonnegative family
  ; alphaBarStrict = alphaStrict family
  ; alphaBelowBar = λ _ → ℚP.≤-refl
  ; baseBelowCeiling = normalizedBaseBelowCeiling family parameter
  ; recurrence = Defect.normalizedDefectRecurrence
      (recurrenceAtThreshold family parameter)
  ; forcingFitsUniformCeiling = λ _ → forcingFitsCeiling family
  }

thresholdUniformNormalizedCeiling :
  (family : ThresholdUniformDefectRecurrenceFamily) →
  ∀ parameter q →
  Defect.normalizedDefectProfile
    (recurrenceAtThreshold family parameter) q
  ≤ ceiling family
thresholdUniformNormalizedCeiling family parameter q =
  Recurrence.variableContractiveRecurrenceUniformCeiling
    (contractiveProfileAtThreshold family parameter) q

uniformRecurrenceDataSufficesForThresholdUniformCeiling : Bool
uniformRecurrenceDataSufficesForThresholdUniformCeiling = true

uniformRecurrenceDataSufficesForThresholdUniformCeilingIsTrue :
  uniformRecurrenceDataSufficesForThresholdUniformCeiling ≡ true
uniformRecurrenceDataSufficesForThresholdUniformCeilingIsTrue = refl
