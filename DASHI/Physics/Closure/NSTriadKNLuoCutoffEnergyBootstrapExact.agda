module DASHI.Physics.Closure.NSTriadKNLuoCutoffEnergyBootstrapExact where

------------------------------------------------------------------------
-- PROVENANCE
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal/year: Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Prove the nonnegative-rational composition used after Luo's cutoff-flux
-- estimate: energy+dissipation is bounded by preceding energy plus flux; flux
-- is bounded by a Schur energy factor times the localized low-pass gradient;
-- and the universal gradient threshold can then be substituted and absorbed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNLocalizedBKMScaleDictionaryExact as Scale

record LuoParabolicTimeCutoff : Set₁ where
  field
    shellIndex : Nat
    shellShift : Nat
    Time : Set
    terminalTime : Time
    cutoffWeight : Time → ℚ
    supportInShiftedParabolicWindow : Set
    cutoffDerivativeBoundByShiftedLambdaSquared : Set
    windowDenominator : Nat
    windowDenominatorMeaning :
      windowDenominator ≡ Scale.parabolicWindowDenominator shellIndex

open LuoParabolicTimeCutoff public

record LuoCutoffEnergyFluxData : Set₁ where
  constructor cutoff-data
  field
    previousCutoffEnergy : ℚ
    currentCutoffEnergy : ℚ
    currentCutoffDissipation : ℚ
    integratedAbsoluteCutoffFlux : ℚ
    cutoffEnergyMajorant : ℚ
    localizedLowPassGradientIntegral : ℚ
    profileSchurConstant : ℚ
    universalGradientThreshold : ℚ

    previousEnergyNonnegative : 0ℚ ≤ previousCutoffEnergy
    currentEnergyNonnegative : 0ℚ ≤ currentCutoffEnergy
    currentDissipationNonnegative : 0ℚ ≤ currentCutoffDissipation
    integratedFluxNonnegative : 0ℚ ≤ integratedAbsoluteCutoffFlux
    energyMajorantNonnegative : 0ℚ ≤ cutoffEnergyMajorant
    localizedGradientNonnegative : 0ℚ ≤ localizedLowPassGradientIntegral
    schurConstantNonnegative : 0ℚ ≤ profileSchurConstant
    universalThresholdNonnegative : 0ℚ ≤ universalGradientThreshold

    highFrequencyEnergyInequality :
      currentCutoffEnergy + currentCutoffDissipation
        ≤ previousCutoffEnergy + integratedAbsoluteCutoffFlux

    integratedFluxEstimate :
      integratedAbsoluteCutoffFlux
        ≤ profileSchurConstant
          * (cutoffEnergyMajorant * localizedLowPassGradientIntegral)

    localizedGradientThresholdSmallness :
      localizedLowPassGradientIntegral ≤ universalGradientThreshold

open LuoCutoffEnergyFluxData public

localizedGradientSubstitution :
  (data : LuoCutoffEnergyFluxData) →
  profileSchurConstant data
    * (cutoffEnergyMajorant data * localizedLowPassGradientIntegral data)
    ≤ profileSchurConstant data
      * (cutoffEnergyMajorant data * universalGradientThreshold data)
localizedGradientSubstitution data =
  let
    instance
      energyNN = nonNegative (energyMajorantNonnegative data)
      schurNN = nonNegative (schurConstantNonnegative data)
    inner = ℚₚ.*-monoˡ-≤-nonNeg
      (cutoffEnergyMajorant data)
      (localizedGradientThresholdSmallness data)
  in
  ℚₚ.*-monoˡ-≤-nonNeg (profileSchurConstant data) inner

integratedFluxBelowThresholdMajorant :
  (data : LuoCutoffEnergyFluxData) →
  integratedAbsoluteCutoffFlux data
    ≤ profileSchurConstant data
      * (cutoffEnergyMajorant data * universalGradientThreshold data)
integratedFluxBelowThresholdMajorant data =
  ℚₚ.≤-trans
    (integratedFluxEstimate data)
    (localizedGradientSubstitution data)

luoSmallTimeEnergyDissipationRecursion :
  (data : LuoCutoffEnergyFluxData) →
  currentCutoffEnergy data + currentCutoffDissipation data
    ≤ previousCutoffEnergy data
      + profileSchurConstant data
        * (cutoffEnergyMajorant data * universalGradientThreshold data)
luoSmallTimeEnergyDissipationRecursion data =
  ℚₚ.≤-trans
    (highFrequencyEnergyInequality data)
    (ℚₚ.+-mono-≤ ℚₚ.≤-refl
      (integratedFluxBelowThresholdMajorant data))

record LuoCutoffBootstrapCertificate
    (data : LuoCutoffEnergyFluxData) : Set where
  constructor bootstrap-certificate
  field
    nextCutoffBudget : ℚ
    nextBudgetNonnegative : 0ℚ ≤ nextCutoffBudget
    recursionRightHandSideBelowBudget :
      previousCutoffEnergy data
        + profileSchurConstant data
          * (cutoffEnergyMajorant data * universalGradientThreshold data)
        ≤ nextCutoffBudget

open LuoCutoffBootstrapCertificate public

luoCutoffBootstrapBound :
  (data : LuoCutoffEnergyFluxData) →
  (certificate : LuoCutoffBootstrapCertificate data) →
  currentCutoffEnergy data + currentCutoffDissipation data
    ≤ nextCutoffBudget certificate
luoCutoffBootstrapBound data certificate =
  ℚₚ.≤-trans
    (luoSmallTimeEnergyDissipationRecursion data)
    (recursionRightHandSideBelowBudget certificate)

record LuoPhysicalEnergyBootstrapAdapter : Set₁ where
  field
    timeCutoff : LuoParabolicTimeCutoff
    cutoffData : LuoCutoffEnergyFluxData
    bootstrap : LuoCutoffBootstrapCertificate cutoffData
    hardLowPassEqualsSourceLowPass : Set
    hardHighPassIsOrthogonalSelfAdjointProjection : Set
    divergenceFreePressureCancellation : Set
    physicalEnergyIdentityMatchesCutoffData : Set
    physicalDissipationMatchesCutoffData : Set
    physicalFluxMatchesIntegratedAbsoluteCutoffFlux : Set
    universalThresholdMatchesLuoDeltaBKMAtUnitViscosity : Set
    bootstrapDecayImpliesRegularity : Set

open LuoPhysicalEnergyBootstrapAdapter public

luoCutoffEnergyFluxAlgebraConstructed : Bool
luoCutoffEnergyFluxAlgebraConstructed = true

luoBootstrapAbsorptionAlgebraConstructed : Bool
luoBootstrapAbsorptionAlgebraConstructed = true

hardHighPassOrthogonalProjectionClosed : Bool
hardHighPassOrthogonalProjectionClosed = false

physicalCutoffEnergyIdentityClosed : Bool
physicalCutoffEnergyIdentityClosed = false

physicalLuoBootstrapAdapterInhabited : Bool
physicalLuoBootstrapAdapterInhabited = false

luoCutoffEnergyFluxAlgebraConstructedIsTrue :
  luoCutoffEnergyFluxAlgebraConstructed ≡ true
luoCutoffEnergyFluxAlgebraConstructedIsTrue = refl

luoBootstrapAbsorptionAlgebraConstructedIsTrue :
  luoBootstrapAbsorptionAlgebraConstructed ≡ true
luoBootstrapAbsorptionAlgebraConstructedIsTrue = refl

hardHighPassOrthogonalProjectionClosedIsFalse :
  hardHighPassOrthogonalProjectionClosed ≡ false
hardHighPassOrthogonalProjectionClosedIsFalse = refl

physicalCutoffEnergyIdentityClosedIsFalse :
  physicalCutoffEnergyIdentityClosed ≡ false
physicalCutoffEnergyIdentityClosedIsFalse = refl

physicalLuoBootstrapAdapterInhabitedIsFalse :
  physicalLuoBootstrapAdapterInhabited ≡ false
physicalLuoBootstrapAdapterInhabitedIsFalse = refl
