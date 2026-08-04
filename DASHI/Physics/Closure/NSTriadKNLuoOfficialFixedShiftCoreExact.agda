module DASHI.Physics.Closure.NSTriadKNLuoOfficialFixedShiftCoreExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Construct the fixed-shift core with its energy and dissipation defined
-- directly from the official threshold-free physical cutoff quantities.
-- Consequently the two canonical carrier-coherence lemmas are reflexivity,
-- rather than separately supplied equalities.
--
-- The genuine analytic leaves remain explicit: the physical fixed-shift
-- recursion, uniform flux-correction absorption and the block-decay
-- certificate identifying the official sequence with the dyadic target.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Rational.Base as ℚBase
open ℚBase using (ℚ)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoPreThresholdCutoffQuantitiesExact as PreQ
import DASHI.Physics.Closure.NSTriadKNLuoPreThresholdPhysicalEnergyTimeExact as PreTime
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftBootstrapFromDerivedBudgetExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

officialCutoffEnergy :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  PreBudget.OfficialLuoPreBudgetData InitialDatum Solution Time →
  Nat → ℚ
officialCutoffEnergy data shell =
  PreQ.currentHardHighEnergy
    (PreTime.cutoffQuantities
      (PreBudget.preThresholdEnergyTimeAt data shell))

officialCutoffDissipation :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  PreBudget.OfficialLuoPreBudgetData InitialDatum Solution Time →
  Nat → ℚ
officialCutoffDissipation data shell =
  PreQ.physicalDissipation
    (PreTime.cutoffQuantities
      (PreBudget.preThresholdEnergyTimeAt data shell))

record OfficialFixedShiftCoreLeaves
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time) : Setω where
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

    localizedGradientIntegral : Nat → ℚ
    integratedFluxCorrection dyadicDecayTarget : Nat → ℚ

    add multiply maximum : ℚ → ℚ → ℚ
    lessOrEqual : ℚ → ℚ → Set

    lessOrEqualMeaning :
      (left right : ℚ) →
      lessOrEqual left right ≡ ℚBase._≤_ left right

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
        (maximum
          (officialCutoffEnergy data shell)
          (officialCutoffDissipation data shell))
        (add
          (multiply correctedShiftCoefficient
            (officialCutoffDissipation data
              (predecessorByFixedShift shell)))
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
      ≡ maximum
          (officialCutoffEnergy data shell)
          (officialCutoffDissipation data shell)

    blockTargetMeaning :
      (shell : Nat) →
      Block.scaledTarget
        (Block.constant blockDecayCertificate)
        (Block.r blockDecayCertificate)
        shell
      ≡ dyadicDecayTarget shell

open OfficialFixedShiftCoreLeaves public

officialFixedShiftCoreInputs :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  OfficialFixedShiftCoreLeaves data →
  Fixed.LuoFixedShiftCoreInputs
officialFixedShiftCoreInputs {data = data} leaves = record
  { alpha = alpha leaves
  ; AlphaInOpenZeroTwo = AlphaInOpenZeroTwo leaves
  ; alphaInOpenZeroTwo = alphaInOpenZeroTwo leaves
  ; blockShift = blockShift leaves
  ; universalDeltaAlpha = universalDeltaAlpha leaves
  ; geometricConstantAlpha = geometricConstantAlpha leaves
  ; parabolicWindowConstant = parabolicWindowConstant leaves
  ; predecessorByFixedShift = predecessorByFixedShift leaves
  ; sufficientlyLarge = sufficientlyLarge leaves
  ; cutoffEnergy = officialCutoffEnergy data
  ; cutoffDissipation = officialCutoffDissipation data
  ; localizedGradientIntegral = localizedGradientIntegral leaves
  ; integratedFluxCorrection = integratedFluxCorrection leaves
  ; dyadicDecayTarget = dyadicDecayTarget leaves
  ; add = add leaves
  ; multiply = multiply leaves
  ; maximum = maximum leaves
  ; lessOrEqual = lessOrEqual leaves
  ; lessOrEqualMeaning = lessOrEqualMeaning leaves
  ; twoMinusAlpha = twoMinusAlpha leaves
  ; halfTwoMinusAlpha = halfTwoMinusAlpha leaves
  ; correctedShiftExponent = correctedShiftExponent leaves
  ; correctedShiftCoefficient = correctedShiftCoefficient leaves
  ; TwoMinusAlphaMeaning = TwoMinusAlphaMeaning leaves
  ; HalfCorrectionMeaning = HalfCorrectionMeaning leaves
  ; CorrectedExponentMeaning = CorrectedExponentMeaning leaves
  ; CorrectedCoefficientMeaning = CorrectedCoefficientMeaning leaves
  ; twoMinusAlphaMeaning = twoMinusAlphaMeaning leaves
  ; halfCorrectionMeaning = halfCorrectionMeaning leaves
  ; correctedExponentMeaning = correctedExponentMeaning leaves
  ; correctedCoefficientMeaning = correctedCoefficientMeaning leaves
  ; fixedShiftRecursion = fixedShiftRecursion leaves
  ; fluxCorrectionAbsorbedUniformly =
      fluxCorrectionAbsorbedUniformly leaves
  ; blockDecayCertificate = blockDecayCertificate leaves
  ; blockSequenceMeaning = blockSequenceMeaning leaves
  ; blockTargetMeaning = blockTargetMeaning leaves
  }

officialFixedShiftEnergyMeaning :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time}
    (leaves : OfficialFixedShiftCoreLeaves data)
    (shell : Nat) →
  Fixed.cutoffEnergy (officialFixedShiftCoreInputs leaves) shell
  ≡ PreQ.currentHardHighEnergy
      (PreTime.cutoffQuantities
        (PreBudget.preThresholdEnergyTimeAt data shell))
officialFixedShiftEnergyMeaning leaves shell = refl

officialFixedShiftDissipationMeaning :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time}
    (leaves : OfficialFixedShiftCoreLeaves data)
    (shell : Nat) →
  Fixed.cutoffDissipation (officialFixedShiftCoreInputs leaves) shell
  ≡ PreQ.physicalDissipation
      (PreTime.cutoffQuantities
        (PreBudget.preThresholdEnergyTimeAt data shell))
officialFixedShiftDissipationMeaning leaves shell = refl

officialFixedShiftEnergyCoherenceDefinitional : Bool
officialFixedShiftEnergyCoherenceDefinitional = true

officialFixedShiftDissipationCoherenceDefinitional : Bool
officialFixedShiftDissipationCoherenceDefinitional = true

officialFixedShiftCoreConstructorClosed : Bool
officialFixedShiftCoreConstructorClosed = true

officialFixedShiftEnergyCoherenceDefinitionalIsTrue :
  officialFixedShiftEnergyCoherenceDefinitional ≡ true
officialFixedShiftEnergyCoherenceDefinitionalIsTrue = refl

officialFixedShiftDissipationCoherenceDefinitionalIsTrue :
  officialFixedShiftDissipationCoherenceDefinitional ≡ true
officialFixedShiftDissipationCoherenceDefinitionalIsTrue = refl

officialFixedShiftCoreConstructorClosedIsTrue :
  officialFixedShiftCoreConstructorClosed ≡ true
officialFixedShiftCoreConstructorClosedIsTrue = refl
