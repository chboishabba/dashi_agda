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
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
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
    dyadicDecayTarget : Shell → Scalar

    lessOrEqual : Scalar → Scalar → Set scalarLevel
    maximum : Scalar → Scalar → Scalar

    localizedCriterionUniform :
      (shell : Shell) → sufficientlyLarge shell →
      lessOrEqual
        (localizedGradientIntegral shell)
        universalDeltaAlpha

    fixedShiftRecursion :
      (shell : Shell) → sufficientlyLarge shell →
      lessOrEqual
        (maximum
          (cutoffEnergy shell)
          (cutoffDissipation shell))
        (maximum
          (cutoffEnergy (predecessorByFixedShift shell))
          (cutoffDissipation (predecessorByFixedShift shell)))

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

    DecayImpliesSection4Summability : Set scalarLevel
    decayImpliesSection4Summability : DecayImpliesSection4Summability

    UniformCutoffFamilyImpliesLimsup : Set scalarLevel
    uniformCutoffFamilyImpliesLimsup :
      UniformCutoffFamilyImpliesLimsup

open LuoAlphaAboveOneRegularityEntry public

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

luoFixedShiftUniformityEnforcedByType : Bool
luoFixedShiftUniformityEnforcedByType = true

luoFixedShiftPhysicalBootstrapInhabited : Bool
luoFixedShiftPhysicalBootstrapInhabited = false

luoFixedShiftUniformBootstrapTargetConstructedIsTrue :
  luoFixedShiftUniformBootstrapTargetConstructed ≡ true
luoFixedShiftUniformBootstrapTargetConstructedIsTrue = refl

luoFixedShiftUniformityEnforcedByTypeIsTrue :
  luoFixedShiftUniformityEnforcedByType ≡ true
luoFixedShiftUniformityEnforcedByTypeIsTrue = refl

luoFixedShiftPhysicalBootstrapInhabitedIsFalse :
  luoFixedShiftPhysicalBootstrapInhabited ≡ false
luoFixedShiftPhysicalBootstrapInhabitedIsFalse = refl
