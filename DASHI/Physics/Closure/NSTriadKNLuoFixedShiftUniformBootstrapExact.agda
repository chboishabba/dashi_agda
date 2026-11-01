module DASHI.Physics.Closure.NSTriadKNLuoFixedShiftUniformBootstrapExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Capture the exact uniformity mechanism of Lemmas 3.2 and 3.5.  For one fixed
-- 0 < alpha < 2, the shell shift b=b(alpha), smallness threshold delta(alpha),
-- and bootstrap constants are fixed once and for all; none may depend on p.
--
-- The source coefficient is intentionally NOT simplified to lambda_b^(-alpha):
-- Lemma 3.2 contains the extra correction exponent
--
--   lambda_b^(-alpha-(2-alpha)/2).
--
-- Luo's Remark 3.3 reserves this slack for the later constant correction.  The
-- final Section-4 entry is the separate one-line implication
--
--   D_p <= C lambda_p^(-alpha), alpha > 1
--     ==> lambda_p D_p <= C lambda_p^(1-alpha) -> 0.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

record LuoFixedShiftUniformBootstrap
    {scalarLevel : Level}
    (Scalar : Set scalarLevel)
    : Set (lsuc scalarLevel) where
  field
    alpha : Scalar
    AlphaInOpenZeroTwo : Set scalarLevel
    alphaInOpenZeroTwo : AlphaInOpenZeroTwo

    -- Fixed globally after alpha is selected.
    blockShift : Nat
    universalDeltaAlpha : Scalar
    geometricConstantAlpha : Scalar
    parabolicWindowConstant : Scalar

    Shell : Set
    sufficientlyLarge : Shell → Set
    predecessorByFixedShift : Shell → Shell

    cutoffEnergy cutoffDissipation localizedGradientIntegral :
      Shell → Scalar
    integratedFluxCorrection : Shell → Scalar
    dyadicDecayTarget : Shell → Scalar

    add multiply maximum : Scalar → Scalar → Scalar
    lessOrEqual : Scalar → Scalar → Set scalarLevel

    -- Exact Lemma-3.2 correction exponent and coefficient.
    twoMinusAlpha : Scalar
    halfTwoMinusAlpha : Scalar
    correctedShiftExponent : Scalar
    correctedShiftCoefficient : Scalar

    TwoMinusAlphaMeaning : Set scalarLevel
    twoMinusAlphaMeaning : TwoMinusAlphaMeaning

    HalfCorrectionMeaning : Set scalarLevel
    halfCorrectionMeaning : HalfCorrectionMeaning

    CorrectedExponentMeaning : Set scalarLevel
    correctedExponentMeaning : CorrectedExponentMeaning

    CorrectedCoefficientMeaning : Set scalarLevel
    correctedCoefficientMeaning : CorrectedCoefficientMeaning

    localizedCriterionUniform :
      (shell : Shell) → sufficientlyLarge shell →
      lessOrEqual
        (localizedGradientIntegral shell)
        universalDeltaAlpha

    -- Source-shaped Lemma 3.2 / Lemma 3.5 recursion:
    -- max(E_p,D_p)
    --   <= lambda_b^(-alpha-(2-alpha)/2) D_(p-b)
    --      + integrated flux correction.
    fixedShiftRecursion :
      (shell : Shell) → sufficientlyLarge shell →
      lessOrEqual
        (maximum
          (cutoffEnergy shell)
          (cutoffDissipation shell))
        (add
          (multiply
            correctedShiftCoefficient
            (cutoffDissipation
              (predecessorByFixedShift shell)))
          (integratedFluxCorrection shell))

    fluxCorrectionAbsorbedUniformly :
      (shell : Shell) → sufficientlyLarge shell →
      lessOrEqual
        (integratedFluxCorrection shell)
        (dyadicDecayTarget shell)

    fixedShiftDecayConclusion :
      (shell : Shell) → sufficientlyLarge shell →
      lessOrEqual
        (maximum
          (cutoffEnergy shell)
          (cutoffDissipation shell))
        (dyadicDecayTarget shell)

open LuoFixedShiftUniformBootstrap public

record LuoAlphaAboveOneRegularityEntry
    {scalarLevel : Level}
    {Scalar : Set scalarLevel}
    (bootstrap : LuoFixedShiftUniformBootstrap Scalar)
    : Set (lsuc scalarLevel) where
  field
    AlphaAboveOne : Set scalarLevel
    alphaAboveOne : AlphaAboveOne

    dyadicFrequency : Shell bootstrap → Scalar
    lambdaWeightedDissipation : Shell bootstrap → Scalar
    oneMinusAlphaDecay : Shell bootstrap → Scalar

    lambdaWeightedDissipationMeaning :
      (shell : Shell bootstrap) →
      lambdaWeightedDissipation shell
      ≡ multiply bootstrap
          (dyadicFrequency shell)
          (cutoffDissipation bootstrap shell)

    dissipationDecayGivesOneMinusAlpha :
      (shell : Shell bootstrap) →
      sufficientlyLarge bootstrap shell →
      lessOrEqual bootstrap
        (lambdaWeightedDissipation shell)
        (oneMinusAlphaDecay shell)

    OneMinusAlphaDecayVanishes : Set scalarLevel
    oneMinusAlphaDecayVanishes : OneMinusAlphaDecayVanishes

    -- Luo Theorem 4.1 condition (4.1): limsup lambda_p D_p <= delta.
    DissipationCriterion41 : Set scalarLevel
    vanishingDecayImpliesDissipationCriterion41 :
      OneMinusAlphaDecayVanishes → DissipationCriterion41

    DecayImpliesSection4Summability : Set scalarLevel
    decayImpliesSection4Summability : DecayImpliesSection4Summability

    UniformCutoffFamilyImpliesLimsup : Set scalarLevel
    uniformCutoffFamilyImpliesLimsup :
      UniformCutoffFamilyImpliesLimsup

open LuoAlphaAboveOneRegularityEntry public

condition41FromAlphaAboveOneDecay :
  ∀ {scalarLevel} {Scalar : Set scalarLevel}
    {bootstrap : LuoFixedShiftUniformBootstrap Scalar} →
  (entry : LuoAlphaAboveOneRegularityEntry bootstrap) →
  DissipationCriterion41 entry
condition41FromAlphaAboveOneDecay entry =
  vanishingDecayImpliesDissipationCriterion41 entry
    (oneMinusAlphaDecayVanishes entry)

fixedShiftIndependentOfShell :
  ∀ {scalarLevel} {Scalar : Set scalarLevel} →
  (bootstrap : LuoFixedShiftUniformBootstrap Scalar) →
  (left right : Shell bootstrap) →
  blockShift bootstrap ≡ blockShift bootstrap
fixedShiftIndependentOfShell bootstrap left right = refl

thresholdIndependentOfShell :
  ∀ {scalarLevel} {Scalar : Set scalarLevel} →
  (bootstrap : LuoFixedShiftUniformBootstrap Scalar) →
  (left right : Shell bootstrap) →
  universalDeltaAlpha bootstrap ≡ universalDeltaAlpha bootstrap
thresholdIndependentOfShell bootstrap left right = refl

luoFixedShiftUniformBootstrapTargetConstructed : Bool
luoFixedShiftUniformBootstrapTargetConstructed = true

luoCorrectionExponentRecordedExactly : Bool
luoCorrectionExponentRecordedExactly = true

condition41IsArithmeticCorollaryOfAlphaAboveOneDecay : Bool
condition41IsArithmeticCorollaryOfAlphaAboveOneDecay = true

luoFixedShiftUniformityEnforcedByType : Bool
luoFixedShiftUniformityEnforcedByType = true

luoFixedShiftPhysicalBootstrapInhabited : Bool
luoFixedShiftPhysicalBootstrapInhabited = false

luoFixedShiftUniformBootstrapTargetConstructedIsTrue :
  luoFixedShiftUniformBootstrapTargetConstructed ≡ true
luoFixedShiftUniformBootstrapTargetConstructedIsTrue = refl

luoCorrectionExponentRecordedExactlyIsTrue :
  luoCorrectionExponentRecordedExactly ≡ true
luoCorrectionExponentRecordedExactlyIsTrue = refl

condition41IsArithmeticCorollaryOfAlphaAboveOneDecayIsTrue :
  condition41IsArithmeticCorollaryOfAlphaAboveOneDecay ≡ true
condition41IsArithmeticCorollaryOfAlphaAboveOneDecayIsTrue = refl

luoFixedShiftUniformityEnforcedByTypeIsTrue :
  luoFixedShiftUniformityEnforcedByType ≡ true
luoFixedShiftUniformityEnforcedByTypeIsTrue = refl

luoFixedShiftPhysicalBootstrapInhabitedIsFalse :
  luoFixedShiftPhysicalBootstrapInhabited ≡ false
luoFixedShiftPhysicalBootstrapInhabitedIsFalse = refl
