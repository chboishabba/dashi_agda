module DASHI.Physics.Closure.NSTriadKNHHBadSelectedThresholdRecurrenceRound47Exact where

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
-- Since the current HH-bad owner consumer needs only one selected threshold,
-- the recurrence coefficients need not be uniform over all delta.  At a fixed
-- physically admissible delta_* it suffices to prove
--
--   B_0 <= delta_* M,
--   B_(q+1) <= (alpha/2) B_q + delta_* 2^(-(q+1)) beta,
--   0 <= alpha < 1,
--   beta <= (1-alpha) M.
--
-- Then C_q = delta_*^(-1) 2^q B_q obeys C_q <= M for every shell.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; cong; trans)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as Scale
import DASHI.Physics.Closure.NSTriadKNHHBadDefectRecurrenceNormalizationRound46Exact as Defect
import DASHI.Physics.Closure.NSTriadKNHHBadVariableProfileRecurrenceRound46Exact as Recurrence

record SelectedThresholdDefectRecurrence : Set where
  field
    parameter : Threshold.PositiveThreshold
    defectRate : Nat → ℚ
    defectRateNonnegative : ∀ q → 0ℚ ≤ defectRate q

    ceiling alpha beta : ℚ
    ceilingNonnegative : 0ℚ ≤ ceiling
    alphaNonnegative : 0ℚ ≤ alpha
    betaNonnegative : 0ℚ ≤ beta
    alphaStrict : alpha < 1ℚ

    baseLinearInSelectedThreshold :
      defectRate zero ≤ Threshold.threshold parameter * ceiling

    oneShellTransfer : ∀ q →
      defectRate (suc q)
      ≤ alpha * Sharp.half * defectRate q
        + Threshold.threshold parameter
          * Sharp.inverseDyadicScale (suc q) * beta

    forcingFitsCeiling : beta ≤ (1ℚ - alpha) * ceiling

open SelectedThresholdDefectRecurrence public

asPhysicalDefectRecurrence :
  (selected : SelectedThresholdDefectRecurrence) →
  Defect.PhysicalDefectShellRecurrence (parameter selected)
asPhysicalDefectRecurrence selected = record
  { defectRate = defectRate selected
  ; alpha = alpha selected
  ; beta = beta selected
  ; defectRateNonnegative = defectRateNonnegative selected
  ; alphaNonnegative = alphaNonnegative selected
  ; betaNonnegative = betaNonnegative selected
  ; oneShellDefectTransfer = oneShellTransfer selected
  }

selectedNormalizedBaseBelowCeiling :
  (selected : SelectedThresholdDefectRecurrence) →
  Defect.normalizedDefectProfile (asPhysicalDefectRecurrence selected) zero
  ≤ ceiling selected
selectedNormalizedBaseBelowCeiling selected =
  let
    p = parameter selected
    inv = Threshold.thresholdInverse p
    delta = Threshold.threshold p
    base = defectRate selected zero
    M = ceiling selected

    scaled : inv * base ≤ inv * (delta * M)
    scaled =
      let instance invNNI = nonNegative (Threshold.thresholdInverseNonnegative p)
      in ℚP.*-monoˡ-≤-nonNeg inv
        (baseLinearInSelectedThreshold selected)

    rightRegroup : inv * (delta * M) ≡ (inv * delta) * M
    rightRegroup = solve (inv ∷ delta ∷ M ∷ [])

    rightMeaning : inv * (delta * M) ≡ M
    rightMeaning =
      trans rightRegroup
        (trans
          (cong (_* M) (Threshold.inverseMeaning p))
          (solve (M ∷ [])))

    leftMeaning :
      inv * base
      ≡ Defect.normalizedDefectProfile
          (asPhysicalDefectRecurrence selected) zero
    leftMeaning = solve (inv ∷ base ∷ [])
  in
  subst
    (λ left → left ≤ M)
    leftMeaning
    (subst
      (λ right → inv * base ≤ right)
      rightMeaning
      scaled)

selectedNormalizedProfileNonnegative :
  (selected : SelectedThresholdDefectRecurrence) →
  ∀ q →
  0ℚ ≤ Defect.normalizedDefectProfile
    (asPhysicalDefectRecurrence selected) q
selectedNormalizedProfileNonnegative selected q =
  let
    p = parameter selected
    instance
      invNNI = nonNegative (Threshold.thresholdInverseNonnegative p)
      scaleNNI = nonNegative (Scale.dyadicScaleNonnegative q)
      invScaleNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (Threshold.thresholdInverse p)
          (Sharp.dyadicScale q)
      defectNNI = nonNegative (defectRateNonnegative selected q)
      totalNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (Threshold.thresholdInverse p * Sharp.dyadicScale q)
          (defectRate selected q)
  in
  ℚP.nonNegative⁻¹
    (Defect.normalizedDefectProfile
      (asPhysicalDefectRecurrence selected) q)

selectedContractiveProfile :
  SelectedThresholdDefectRecurrence →
  Recurrence.VariableContractiveProfileRecurrence
selectedContractiveProfile selected = record
  { profile = Defect.normalizedDefectProfile (asPhysicalDefectRecurrence selected)
  ; alpha = λ _ → alpha selected
  ; beta = λ _ → beta selected
  ; alphaBar = alpha selected
  ; ceiling = ceiling selected
  ; profileNonnegative = selectedNormalizedProfileNonnegative selected
  ; alphaNonnegative = λ _ → alphaNonnegative selected
  ; betaNonnegative = λ _ → betaNonnegative selected
  ; ceilingNonnegative = ceilingNonnegative selected
  ; alphaBarNonnegative = alphaNonnegative selected
  ; alphaBarStrict = alphaStrict selected
  ; alphaBelowBar = λ _ → ℚP.≤-refl
  ; baseBelowCeiling = selectedNormalizedBaseBelowCeiling selected
  ; recurrence = Defect.normalizedDefectRecurrence
      (asPhysicalDefectRecurrence selected)
  ; forcingFitsUniformCeiling = λ _ → forcingFitsCeiling selected
  }

selectedThresholdUniformShellCeiling :
  (selected : SelectedThresholdDefectRecurrence) →
  ∀ q →
  Defect.normalizedDefectProfile
    (asPhysicalDefectRecurrence selected) q
  ≤ ceiling selected
selectedThresholdUniformShellCeiling selected q =
  Recurrence.variableContractiveRecurrenceUniformCeiling
    (selectedContractiveProfile selected) q

selectedThresholdRecurrenceClosesShellUniformProfile : Bool
selectedThresholdRecurrenceClosesShellUniformProfile = true

selectedThresholdRecurrenceClosesShellUniformProfileIsTrue :
  selectedThresholdRecurrenceClosesShellUniformProfile ≡ true
selectedThresholdRecurrenceClosesShellUniformProfileIsTrue = refl
