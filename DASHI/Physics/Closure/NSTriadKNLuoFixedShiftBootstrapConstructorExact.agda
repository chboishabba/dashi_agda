module DASHI.Physics.Closure.NSTriadKNLuoFixedShiftBootstrapConstructorExact where

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
-- Construct the rational fixed-shift bootstrap while deriving its decay
-- conclusion from the exact block induction theorem.  The caller supplies the
-- source recursion/correction certificate and literal identifications with the
-- physical energy/dissipation sequence; it cannot independently assert the
-- final shell-uniform decay.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftUniformBootstrapExact as Uniform
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

record LuoFixedShiftBootstrapInputs : Set₁ where
  field
    alpha : ℚ
    AlphaInOpenZeroTwo : Set
    alphaInOpenZeroTwo : AlphaInOpenZeroTwo

    blockShift : Nat
    universalDeltaAlpha : ℚ
    geometricConstantAlpha : ℚ
    parabolicWindowConstant : ℚ

    predecessorByFixedShift : Nat → Nat
    sufficientlyLarge : Nat → Set

    cutoffEnergy cutoffDissipation localizedGradientIntegral : Nat → ℚ
    integratedFluxCorrection dyadicDecayTarget : Nat → ℚ

    add multiply maximum : ℚ → ℚ → ℚ
    lessOrEqual : ℚ → ℚ → Set

    twoMinusAlpha halfTwoMinusAlpha correctedShiftExponent : ℚ
    correctedShiftCoefficient : ℚ

    TwoMinusAlphaMeaning HalfCorrectionMeaning : Set
    CorrectedExponentMeaning CorrectedCoefficientMeaning : Set

    twoMinusAlphaMeaning : TwoMinusAlphaMeaning
    halfCorrectionMeaning : HalfCorrectionMeaning
    correctedExponentMeaning : CorrectedExponentMeaning
    correctedCoefficientMeaning : CorrectedCoefficientMeaning

    localizedCriterionUniform :
      (shell : Nat) → sufficientlyLarge shell →
      lessOrEqual
        (localizedGradientIntegral shell)
        universalDeltaAlpha

    fixedShiftRecursion :
      (shell : Nat) → sufficientlyLarge shell →
      lessOrEqual
        (maximum (cutoffEnergy shell) (cutoffDissipation shell))
        (add
          (multiply correctedShiftCoefficient
            (cutoffDissipation (predecessorByFixedShift shell)))
          (integratedFluxCorrection shell))

    fluxCorrectionAbsorbedUniformly :
      (shell : Nat) → sufficientlyLarge shell →
      lessOrEqual
        (integratedFluxCorrection shell)
        (dyadicDecayTarget shell)

    blockDecayCertificate : Block.RationalFixedBlockDecay

    blockSequenceMeaning :
      (shell : Nat) →
      Block.sequence blockDecayCertificate shell
      ≡ maximum (cutoffEnergy shell) (cutoffDissipation shell)

    blockTargetMeaning :
      (shell : Nat) →
      Block.scaledTarget
        (Block.constant blockDecayCertificate)
        (Block.r blockDecayCertificate)
        shell
      ≡ dyadicDecayTarget shell

open LuoFixedShiftBootstrapInputs public

derivedFixedShiftDecayConclusion :
  (inputs : LuoFixedShiftBootstrapInputs) →
  (shell : Nat) → sufficientlyLarge inputs shell →
  lessOrEqual inputs
    (maximum inputs
      (cutoffEnergy inputs shell)
      (cutoffDissipation inputs shell))
    (dyadicDecayTarget inputs shell)
derivedFixedShiftDecayConclusion inputs shell large =
  subst
    (λ left →
      lessOrEqual inputs left (dyadicDecayTarget inputs shell))
    (blockSequenceMeaning inputs shell)
    (subst
      (λ right →
        lessOrEqual inputs
          (Block.sequence (blockDecayCertificate inputs) shell)
          right)
      (blockTargetMeaning inputs shell)
      (Block.fixedBlockDecay (blockDecayCertificate inputs) shell))

luoFixedShiftBootstrap :
  LuoFixedShiftBootstrapInputs →
  Uniform.LuoFixedShiftUniformBootstrap ℚ
luoFixedShiftBootstrap inputs = record
  { alpha = alpha inputs
  ; AlphaInOpenZeroTwo = AlphaInOpenZeroTwo inputs
  ; alphaInOpenZeroTwo = alphaInOpenZeroTwo inputs
  ; blockShift = blockShift inputs
  ; universalDeltaAlpha = universalDeltaAlpha inputs
  ; geometricConstantAlpha = geometricConstantAlpha inputs
  ; parabolicWindowConstant = parabolicWindowConstant inputs
  ; Shell = Nat
  ; sufficientlyLarge = sufficientlyLarge inputs
  ; predecessorByFixedShift = predecessorByFixedShift inputs
  ; cutoffEnergy = cutoffEnergy inputs
  ; cutoffDissipation = cutoffDissipation inputs
  ; localizedGradientIntegral = localizedGradientIntegral inputs
  ; integratedFluxCorrection = integratedFluxCorrection inputs
  ; dyadicDecayTarget = dyadicDecayTarget inputs
  ; add = add inputs
  ; multiply = multiply inputs
  ; maximum = maximum inputs
  ; lessOrEqual = lessOrEqual inputs
  ; twoMinusAlpha = twoMinusAlpha inputs
  ; halfTwoMinusAlpha = halfTwoMinusAlpha inputs
  ; correctedShiftExponent = correctedShiftExponent inputs
  ; correctedShiftCoefficient = correctedShiftCoefficient inputs
  ; TwoMinusAlphaMeaning = TwoMinusAlphaMeaning inputs
  ; twoMinusAlphaMeaning = twoMinusAlphaMeaning inputs
  ; HalfCorrectionMeaning = HalfCorrectionMeaning inputs
  ; halfCorrectionMeaning = halfCorrectionMeaning inputs
  ; CorrectedExponentMeaning = CorrectedExponentMeaning inputs
  ; correctedExponentMeaning = correctedExponentMeaning inputs
  ; CorrectedCoefficientMeaning = CorrectedCoefficientMeaning inputs
  ; correctedCoefficientMeaning = correctedCoefficientMeaning inputs
  ; localizedCriterionUniform = localizedCriterionUniform inputs
  ; fixedShiftRecursion = fixedShiftRecursion inputs
  ; fluxCorrectionAbsorbedUniformly =
      fluxCorrectionAbsorbedUniformly inputs
  ; fixedShiftDecayConclusion =
      derivedFixedShiftDecayConclusion inputs
  }

fixedShiftDecayConclusionDerivedByInduction : Bool
fixedShiftDecayConclusionDerivedByInduction = true

fixedShiftDecayConclusionDerivedByInductionIsTrue :
  fixedShiftDecayConclusionDerivedByInduction ≡ true
fixedShiftDecayConclusionDerivedByInductionIsTrue = refl
