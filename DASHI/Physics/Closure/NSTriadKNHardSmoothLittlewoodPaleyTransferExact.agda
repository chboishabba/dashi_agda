module DASHI.Physics.Closure.NSTriadKNHardSmoothLittlewoodPaleyTransferExact where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011. DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal/year: Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Isolate the exact finite-band/norm transport required between DASHI's sharp
-- periodic hard cutoff and Luo's smooth Littlewood--Paley low-pass.  Given a
-- uniform comparison constant C_band and a hard-projector terminal-window
-- budget, the smooth Luo quantity is below the universal threshold whenever
-- C_band times the hard budget is below that threshold.
--
-- The algebra is proved here.  Construction of the concrete smooth multiplier
-- family and its uniform finite-band constant remains a separate analytic
-- inhabitant, not an assumed equality of projector conventions.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ

------------------------------------------------------------------------
-- Support-level finite-band interface.
------------------------------------------------------------------------

infix 4 _∈Nat_
data _∈Nat_ (value : Nat) : List Nat → Set where
  here : ∀ {values} → value ∈Nat (value ∷ values)
  there : ∀ {head values} → value ∈Nat values → value ∈Nat (head ∷ values)

record SmoothShellHardBandSupport {m : Level} (Mode : Set m) : Set (lsuc m) where
  field
    smoothShellSupported : Nat → Mode → Set m
    hardShellSupported : Nat → Mode → Set m
    hardBand : Nat → List Nat

    smoothSupportOccursInHardBand :
      ∀ shell mode →
      smoothShellSupported shell mode →
      Σ Nat (λ hardShell →
        (hardShell ∈Nat hardBand shell)
          × hardShellSupported hardShell mode)

open SmoothShellHardBandSupport public

------------------------------------------------------------------------
-- Norm and terminal-window comparison.
------------------------------------------------------------------------

record HardSmoothLowPassGradientComparison : Set where
  constructor comparison
  field
    shellIndex : Nat
    hardLowPassGradientInfinity : ℚ
    smoothLowPassGradientInfinity : ℚ
    finiteBandConstant : ℚ

    hardGradientNonnegative : 0ℚ ≤ hardLowPassGradientInfinity
    smoothGradientNonnegative : 0ℚ ≤ smoothLowPassGradientInfinity
    finiteBandConstantNonnegative : 0ℚ ≤ finiteBandConstant

    smoothGradientBelowFiniteBandHardGradient :
      smoothLowPassGradientInfinity
        ≤ finiteBandConstant * hardLowPassGradientInfinity

open HardSmoothLowPassGradientComparison public

record HardSmoothTerminalWindowComparison : Set where
  constructor terminal-comparison
  field
    shellIndex : Nat
    hardTerminalWindowIntegral : ℚ
    smoothLuoTerminalWindowIntegral : ℚ
    hardTerminalWindowBudget : ℚ
    luoUniversalThreshold : ℚ
    finiteBandConstant : ℚ

    hardIntegralNonnegative : 0ℚ ≤ hardTerminalWindowIntegral
    smoothIntegralNonnegative : 0ℚ ≤ smoothLuoTerminalWindowIntegral
    hardBudgetNonnegative : 0ℚ ≤ hardTerminalWindowBudget
    thresholdNonnegative : 0ℚ ≤ luoUniversalThreshold
    finiteBandConstantNonnegative : 0ℚ ≤ finiteBandConstant

    smoothIntegralBelowFiniteBandHardIntegral :
      smoothLuoTerminalWindowIntegral
        ≤ finiteBandConstant * hardTerminalWindowIntegral

    hardIntegralBelowBudget :
      hardTerminalWindowIntegral ≤ hardTerminalWindowBudget

    scaledHardBudgetBelowLuoThreshold :
      finiteBandConstant * hardTerminalWindowBudget
        ≤ luoUniversalThreshold

open HardSmoothTerminalWindowComparison public

finiteBandHardIntegralBelowScaledBudget :
  (comparison : HardSmoothTerminalWindowComparison) →
  finiteBandConstant comparison * hardTerminalWindowIntegral comparison
    ≤ finiteBandConstant comparison * hardTerminalWindowBudget comparison
finiteBandHardIntegralBelowScaledBudget comparison =
  let
    instance
      bandNN = nonNegative (finiteBandConstantNonnegative comparison)
  in
  ℚₚ.*-monoˡ-≤-nonNeg
    (finiteBandConstant comparison)
    (hardIntegralBelowBudget comparison)

hardTerminalWindowBudgetTransfersToLuoSmoothCriterion :
  (comparison : HardSmoothTerminalWindowComparison) →
  smoothLuoTerminalWindowIntegral comparison
    ≤ luoUniversalThreshold comparison
hardTerminalWindowBudgetTransfersToLuoSmoothCriterion comparison =
  ℚₚ.≤-trans
    (smoothIntegralBelowFiniteBandHardIntegral comparison)
    (ℚₚ.≤-trans
      (finiteBandHardIntegralBelowScaledBudget comparison)
      (scaledHardBudgetBelowLuoThreshold comparison))

hardSmoothFiniteBandTransferAlgebraConstructed : Bool
hardSmoothFiniteBandTransferAlgebraConstructed = true

hardSmoothTerminalWindowTransferConstructed : Bool
hardSmoothTerminalWindowTransferConstructed = true

concreteSmoothPeriodicMultiplierFamilyConstructed : Bool
concreteSmoothPeriodicMultiplierFamilyConstructed = false

uniformHardSmoothFiniteBandConstantConstructed : Bool
uniformHardSmoothFiniteBandConstantConstructed = false

hardSmoothFiniteBandTransferAlgebraConstructedIsTrue :
  hardSmoothFiniteBandTransferAlgebraConstructed ≡ true
hardSmoothFiniteBandTransferAlgebraConstructedIsTrue = refl

hardSmoothTerminalWindowTransferConstructedIsTrue :
  hardSmoothTerminalWindowTransferConstructed ≡ true
hardSmoothTerminalWindowTransferConstructedIsTrue = refl

concreteSmoothPeriodicMultiplierFamilyConstructedIsFalse :
  concreteSmoothPeriodicMultiplierFamilyConstructed ≡ false
concreteSmoothPeriodicMultiplierFamilyConstructedIsFalse = refl

uniformHardSmoothFiniteBandConstantConstructedIsFalse :
  uniformHardSmoothFiniteBandConstantConstructed ≡ false
uniformHardSmoothFiniteBandConstantConstructedIsFalse = refl
