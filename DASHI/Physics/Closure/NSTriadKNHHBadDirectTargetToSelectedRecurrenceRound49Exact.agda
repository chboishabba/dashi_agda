module DASHI.Physics.Closure.NSTriadKNHHBadDirectTargetToSelectedRecurrenceRound49Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- This is the radical-free elimination promised by the Round-49 analysis.
-- Starting from the actual normalized physical recurrence C_(q+1)<=alpha C_q+beta,
-- the two strict numerical inequalities
--
--   C_0 < T,
--   beta < (1-alpha) T
--
-- construct an explicit positive slack, hence a ceiling M<T, and therefore
-- the mature selected-threshold recurrence witness.  The caller never chooses
-- or optimizes M.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (zero)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadDefectRecurrenceNormalizationRound46Exact as Defect
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedThresholdRecurrenceRound47Exact as Selected
import DASHI.Physics.Closure.NSTriadKNHHBadStrictTargetInterpolationRound49Exact as Interp

record DirectPhysicalHHBadTarget
    (parameter : Threshold.PositiveThreshold) : Set where
  field
    physicalRecurrence : Defect.PhysicalDefectShellRecurrence parameter
    target : ℚ
    alphaStrict : Defect.alpha physicalRecurrence < 1ℚ

    normalizedBaseStrict :
      Defect.normalizedDefectProfile physicalRecurrence zero < target

    forcingStrict :
      Defect.beta physicalRecurrence
      < (1ℚ - Defect.alpha physicalRecurrence) * target

open DirectPhysicalHHBadTarget public

strictTargetData :
  ∀ {parameter} →
  DirectPhysicalHHBadTarget parameter →
  Interp.StrictHHBadTarget
strictTargetData input = record
  { base = Defect.normalizedDefectProfile r zero
  ; alpha = Defect.alpha r
  ; beta = Defect.beta r
  ; target = target input
  ; baseNonnegative = baseNN
  ; alphaNonnegative = Defect.alphaNonnegative r
  ; betaNonnegative = Defect.betaNonnegative r
  ; alphaStrict = alphaStrict input
  ; baseStrict = normalizedBaseStrict input
  ; forcingStrict = forcingStrict input
  }
  where
  r = physicalRecurrence input

  baseNN : 0ℚ ≤ Defect.normalizedDefectProfile r zero
  baseNN =
    let
      factorNN = Defect.normalizationFactorNonnegative r zero
      defectNN = Defect.defectRateNonnegative r zero
      instance
        factorNNI = nonNegative factorNN
        defectNNI = nonNegative defectNN
        totalNNI = ℚP.nonNeg*nonNeg⇒nonNeg
          (Defect.normalizationFactor r zero)
          (Defect.defectRate r zero)
    in
    ℚP.nonNegative⁻¹ (Defect.normalizedDefectProfile r zero)

derivedTargetCeiling :
  ∀ {parameter} → DirectPhysicalHHBadTarget parameter → ℚ
derivedTargetCeiling input = Interp.derivedCeiling (strictTargetData input)

derivedTargetCeilingStrict :
  ∀ {parameter} (input : DirectPhysicalHHBadTarget parameter) →
  derivedTargetCeiling input < target input
derivedTargetCeilingStrict input =
  Interp.derivedCeilingStrict (strictTargetData input)

rawBaseBelowDerivedCeiling :
  ∀ {parameter} (input : DirectPhysicalHHBadTarget parameter) →
  Defect.defectRate (physicalRecurrence input) zero
  ≤ Threshold.threshold parameter * derivedTargetCeiling input
rawBaseBelowDerivedCeiling {parameter} input =
  let
    r = physicalRecurrence input
    C0 = Defect.normalizedDefectProfile r zero
    M = derivedTargetCeiling input
    delta = Threshold.threshold parameter
    inv = Threshold.thresholdInverse parameter
    B0 = Defect.defectRate r zero

    C0below : C0 ≤ M
    C0below = Interp.baseBelowDerivedCeiling (strictTargetData input)

    scaled : delta * C0 ≤ delta * M
    scaled =
      let instance deltaNNI = nonNegative (Threshold.thresholdNonnegative parameter)
      in ℚP.*-monoˡ-≤-nonNeg delta C0below

    leftMeaning : delta * C0 ≡ B0
    leftMeaning =
      let
        regroup : delta * (inv * B0) ≡ (inv * delta) * B0
        regroup = solve (delta ∷ inv ∷ B0 ∷ [])
      in
      trans
        (solve (delta ∷ inv ∷ B0 ∷ []))
        (trans
          (cong (_* B0) (Threshold.inverseMeaning parameter))
          (solve (B0 ∷ [])))
  in
  subst
    (λ left → left ≤ delta * M)
    leftMeaning
    scaled

selectedRecurrenceFromDirectTargets :
  ∀ {parameter} →
  DirectPhysicalHHBadTarget parameter →
  Selected.SelectedThresholdDefectRecurrence
selectedRecurrenceFromDirectTargets {parameter} input = record
  { parameter = parameter
  ; defectRate = Defect.defectRate r
  ; defectRateNonnegative = Defect.defectRateNonnegative r
  ; ceiling = derivedTargetCeiling input
  ; alpha = Defect.alpha r
  ; beta = Defect.beta r
  ; ceilingNonnegative = Interp.derivedCeilingNonnegative (strictTargetData input)
  ; alphaNonnegative = Defect.alphaNonnegative r
  ; betaNonnegative = Defect.betaNonnegative r
  ; alphaStrict = alphaStrict input
  ; baseLinearInSelectedThreshold = rawBaseBelowDerivedCeiling input
  ; oneShellTransfer = Defect.oneShellDefectTransfer r
  ; forcingFitsCeiling = Interp.forcingBelowDerivedCeiling (strictTargetData input)
  }
  where
  r = physicalRecurrence input

directTargetsGiveUniformProfileBelowStrictGate :
  ∀ {parameter}
    (input : DirectPhysicalHHBadTarget parameter) q →
  Defect.normalizedDefectProfile
    (Selected.asPhysicalDefectRecurrence
      (selectedRecurrenceFromDirectTargets input)) q
  ≤ derivedTargetCeiling input
directTargetsGiveUniformProfileBelowStrictGate input q =
  Selected.selectedThresholdUniformShellCeiling
    (selectedRecurrenceFromDirectTargets input) q

hhBadDirectStrictTargetsCompileToSelectedWitness : Bool
hhBadDirectStrictTargetsCompileToSelectedWitness = true

hhBadDirectStrictTargetsCompileToSelectedWitnessIsTrue :
  hhBadDirectStrictTargetsCompileToSelectedWitness ≡ true
hhBadDirectStrictTargetsCompileToSelectedWitnessIsTrue = refl
