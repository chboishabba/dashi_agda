module DASHI.Physics.Closure.NSTriadKNLuoFixedShiftBootstrapFromDerivedBudgetExact where

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
-- Construct the fixed-b bootstrap inputs without accepting Luo's localized
-- gradient hypothesis as an independent field. The hypothesis is derived from
-- a non-circular hard-window budget family and the already-selected uniform
-- hard/smooth multiplier theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoConcreteRadialMultiplierKernelExact as Multiplier
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicMultiplierKernelBoundExact as MultiplierAbstract
import DASHI.Physics.Closure.NSTriadKNLuoOfficialLerayHopfAuthorityExact as OfficialLuo
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftBootstrapConstructorExact as Constructor
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

record LuoFixedShiftCoreInputs : Set₁ where
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

    lessOrEqualMeaning :
      (left right : ℚ) →
      lessOrEqual left right ≡ Data.Rational.Base._≤_ left right

    twoMinusAlpha halfTwoMinusAlpha correctedShiftExponent : ℚ
    correctedShiftCoefficient : ℚ

    TwoMinusAlphaMeaning HalfCorrectionMeaning : Set
    CorrectedExponentMeaning CorrectedCoefficientMeaning : Set

    twoMinusAlphaMeaning : TwoMinusAlphaMeaning
    halfCorrectionMeaning : HalfCorrectionMeaning
    correctedExponentMeaning : CorrectedExponentMeaning
    correctedCoefficientMeaning : CorrectedCoefficientMeaning

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

open LuoFixedShiftCoreInputs public

record FixedShiftBudgetIdentification
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time)
    (budgets : PreBudget.DerivedLuoTerminalBudgetFamily data)
    (core : LuoFixedShiftCoreInputs) : Setω where
  field
    localizedGradientIsSmoothTerminalIntegral :
      (shell : Nat) →
      localizedGradientIntegral core shell
      ≡
      MultiplierAbstract.smoothTerminalWindowIntegral
        (Multiplier.canonicalLuoMultiplierAuthority
          (PreBudget.multiplierRealization data))
        shell (PreBudget.solution data)

    universalThresholdIsLuoDelta :
      universalDeltaAlpha core
      ≡ OfficialLuo.universalDeltaBKM (PreBudget.sourceCarrier data)

open FixedShiftBudgetIdentification public

localizedCriterionFromDerivedBudget :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time}
    {budgets : PreBudget.DerivedLuoTerminalBudgetFamily data}
    {core : LuoFixedShiftCoreInputs} →
  (identification : FixedShiftBudgetIdentification data budgets core) →
  (shell : Nat) → sufficientlyLarge core shell →
  lessOrEqual core
    (localizedGradientIntegral core shell)
    (universalDeltaAlpha core)
localizedCriterionFromDerivedBudget
  {data = data} {budgets = budgets} {core = core}
  identification shell large
  rewrite lessOrEqualMeaning core
            (localizedGradientIntegral core shell)
            (universalDeltaAlpha core)
        | localizedGradientIsSmoothTerminalIntegral identification shell
        | universalThresholdIsLuoDelta identification =
  MultiplierAbstract.luoSmoothCriterionFromHardBudget
    (Multiplier.canonicalLuoMultiplierAuthority
      (PreBudget.multiplierRealization data))
    shell
    (PreBudget.solution data)
    (PreBudget.derivedTerminalBudgetAt budgets shell)

fixedShiftBootstrapInputsFromDerivedBudget :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time}
    {budgets : PreBudget.DerivedLuoTerminalBudgetFamily data} →
  (core : LuoFixedShiftCoreInputs) →
  FixedShiftBudgetIdentification data budgets core →
  Constructor.LuoFixedShiftBootstrapInputs
fixedShiftBootstrapInputsFromDerivedBudget
  {data = data} {budgets = budgets} core identification = record
  { alpha = alpha core
  ; AlphaInOpenZeroTwo = AlphaInOpenZeroTwo core
  ; alphaInOpenZeroTwo = alphaInOpenZeroTwo core
  ; blockShift = blockShift core
  ; universalDeltaAlpha = universalDeltaAlpha core
  ; geometricConstantAlpha = geometricConstantAlpha core
  ; parabolicWindowConstant = parabolicWindowConstant core
  ; predecessorByFixedShift = predecessorByFixedShift core
  ; sufficientlyLarge = sufficientlyLarge core
  ; cutoffEnergy = cutoffEnergy core
  ; cutoffDissipation = cutoffDissipation core
  ; localizedGradientIntegral = localizedGradientIntegral core
  ; integratedFluxCorrection = integratedFluxCorrection core
  ; dyadicDecayTarget = dyadicDecayTarget core
  ; add = add core
  ; multiply = multiply core
  ; maximum = maximum core
  ; lessOrEqual = lessOrEqual core
  ; lessOrEqualMeaning = lessOrEqualMeaning core
  ; twoMinusAlpha = twoMinusAlpha core
  ; halfTwoMinusAlpha = halfTwoMinusAlpha core
  ; correctedShiftExponent = correctedShiftExponent core
  ; correctedShiftCoefficient = correctedShiftCoefficient core
  ; TwoMinusAlphaMeaning = TwoMinusAlphaMeaning core
  ; HalfCorrectionMeaning = HalfCorrectionMeaning core
  ; CorrectedExponentMeaning = CorrectedExponentMeaning core
  ; CorrectedCoefficientMeaning = CorrectedCoefficientMeaning core
  ; twoMinusAlphaMeaning = twoMinusAlphaMeaning core
  ; halfCorrectionMeaning = halfCorrectionMeaning core
  ; correctedExponentMeaning = correctedExponentMeaning core
  ; correctedCoefficientMeaning = correctedCoefficientMeaning core
  ; localizedCriterionUniform =
      localizedCriterionFromDerivedBudget identification
  ; fixedShiftRecursion = fixedShiftRecursion core
  ; fluxCorrectionAbsorbedUniformly =
      fluxCorrectionAbsorbedUniformly core
  ; blockDecayCertificate = blockDecayCertificate core
  ; blockSequenceMeaning = blockSequenceMeaning core
  ; blockTargetMeaning = blockTargetMeaning core
  }

localizedCriterionDerivedFromBudget : Bool
localizedCriterionDerivedFromBudget = true

localizedCriterionDerivedFromBudgetIsTrue :
  localizedCriterionDerivedFromBudget ≡ true
localizedCriterionDerivedFromBudgetIsTrue = refl
