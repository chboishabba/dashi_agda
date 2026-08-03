module DASHI.Physics.Closure.NSTriadKNLuoPrimarySourceProofArchitectureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal/year: Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- SCOPE
-- Record the literal source architecture used by the DASHI implementation.
-- Theorem 1.1 controls the full gradient of the low-pass velocity on the
-- parabolic window T-c lambda_p^{-2}.  The constants are universal after the
-- paper's viscosity normalization nu=1.  Proposition 3.1 supplies the cutoff
-- energy-flux estimate, and the subsequent small-time cutoff-energy and
-- cutoff-dissipation estimates feed the bootstrap.
--
-- No external theorem is imported as an Agda axiom here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNLocalizedBKMScaleDictionaryExact as Scale

record LuoTheorem11Target : Set₁ where
  field
    PeriodicOrEuclideanSolution : Set
    RegularOnOpenInterval : PeriodicOrEuclideanSolution → Set
    RegularThroughTerminalTime : PeriodicOrEuclideanSolution → Set

    solution : PeriodicOrEuclideanSolution
    terminalTime : Set

    viscosityNormalizedToOne : Set
    shellIndex : Nat
    dyadicWavenumber : Nat
    dyadicWavenumberMeaning :
      dyadicWavenumber ≡ Scale.shellWavenumber shellIndex

    parabolicWindow : Set
    fullLowPassGradientInfinityIntegral : Set
    universalDeltaBKM : Set
    limsupBelowUniversalDeltaBKM : Set
    criterionImpliesRegularity : Set

record LuoProposition31FluxTarget : Set₁ where
  field
    cutoffIndex : Nat
    cutoffEnergyFlux : Set
    lowShellWeightedEnergy : Set
    highShellEnergy : Set
    fullLowPassGradientInfinity : Set
    fluxBoundByEnergyMajorantTimesLowPassGradient : Set

record LuoSmallTimeEnergyDissipationTarget : Set₁ where
  field
    cutoffIndex : Nat
    shellShift : Nat
    cutoffEnergy : Set
    cutoffDissipation : Set
    shiftedParabolicWindow : Set
    timeCutoffDerivativeBound : Set
    precedingScaleLeakage : Set
    integratedCutoffFlux : Set
    smallTimeRecursion : Set
    bootstrapAbsorption : Set

luoTheorem11LiteralShapeRecorded : Bool
luoTheorem11LiteralShapeRecorded = true

luoTargetIsFullLowPassGradient : Bool
luoTargetIsFullLowPassGradient = true

luoUniversalConstantsUnderUnitViscosityRecorded : Bool
luoUniversalConstantsUnderUnitViscosityRecorded = true

luoProposition31FluxArchitectureRecorded : Bool
luoProposition31FluxArchitectureRecorded = true

luoSmallTimeEnergyDissipationArchitectureRecorded : Bool
luoSmallTimeEnergyDissipationArchitectureRecorded = true

luoExternalContinuationTheoremImported : Bool
luoExternalContinuationTheoremImported = false

luoTheorem11LiteralShapeRecordedIsTrue :
  luoTheorem11LiteralShapeRecorded ≡ true
luoTheorem11LiteralShapeRecordedIsTrue = refl

luoTargetIsFullLowPassGradientIsTrue :
  luoTargetIsFullLowPassGradient ≡ true
luoTargetIsFullLowPassGradientIsTrue = refl

luoUniversalConstantsUnderUnitViscosityRecordedIsTrue :
  luoUniversalConstantsUnderUnitViscosityRecorded ≡ true
luoUniversalConstantsUnderUnitViscosityRecordedIsTrue = refl

luoProposition31FluxArchitectureRecordedIsTrue :
  luoProposition31FluxArchitectureRecorded ≡ true
luoProposition31FluxArchitectureRecordedIsTrue = refl

luoSmallTimeEnergyDissipationArchitectureRecordedIsTrue :
  luoSmallTimeEnergyDissipationArchitectureRecorded ≡ true
luoSmallTimeEnergyDissipationArchitectureRecordedIsTrue = refl

luoExternalContinuationTheoremImportedIsFalse :
  luoExternalContinuationTheoremImported ≡ false
luoExternalContinuationTheoremImportedIsFalse = refl
