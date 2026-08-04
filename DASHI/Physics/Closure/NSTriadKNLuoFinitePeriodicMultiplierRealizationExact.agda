module DASHI.Physics.Closure.NSTriadKNLuoFinitePeriodicMultiplierRealizationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- PURPOSE
-- Construct the canonical periodic multiplier realization from exact finite
-- convolution receipts. The finite Young reducer proves the scalar bounds;
-- the caller identifies those sums with the smooth observables and their
-- majorants with C_chi times the hard observables.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSignedConvolutionYoungExact as Young
import DASHI.Physics.Closure.NSTriadKNLuoConcreteRadialMultiplierKernelExact as Multiplier

record FinitePeriodicMultiplierInputs
    {stateLevel pointLevel : Level}
    (State : Set stateLevel)
    (TorusPoint : Set pointLevel)
    : Set (lsuc (stateLevel ⊔ pointLevel)) where
  field
    kernelTheorem : Multiplier.PeriodizedDyadicKernelL1Theorem TorusPoint

    hardGradientInfinity : Nat → State → ℚ
    smoothGradientInfinity : Nat → State → ℚ
    hardTerminalWindowIntegral : Nat → State → ℚ
    smoothTerminalWindowIntegral : Nat → State → ℚ

    hardGradientNonnegative :
      ∀ shell state → 0ℚ ≤ hardGradientInfinity shell state
    smoothGradientNonnegative :
      ∀ shell state → 0ℚ ≤ smoothGradientInfinity shell state
    hardTerminalIntegralNonnegative :
      ∀ shell state → 0ℚ ≤ hardTerminalWindowIntegral shell state
    smoothTerminalIntegralNonnegative :
      ∀ shell state → 0ℚ ≤ smoothTerminalWindowIntegral shell state

    gradientConvolution :
      Nat → State → Young.FiniteSignedConvolutionYoungData
    terminalConvolution :
      Nat → State → Young.FiniteSignedConvolutionYoungData

    gradientSignedSumMeaning :
      (shell : Nat) → (state : State) →
      Majorant.sumTo
        (Young.signedTerm (gradientConvolution shell state))
        (Young.cutoff (gradientConvolution shell state))
      ≡ smoothGradientInfinity shell state

    gradientMajorantMeaning :
      (shell : Nat) → (state : State) →
      Young.l1TimesSupBound (gradientConvolution shell state)
      ≡ Multiplier.euclideanInverseTransformL1Norm kernelTheorem
          * hardGradientInfinity shell state

    terminalSignedSumMeaning :
      (shell : Nat) → (state : State) →
      Majorant.sumTo
        (Young.signedTerm (terminalConvolution shell state))
        (Young.cutoff (terminalConvolution shell state))
      ≡ smoothTerminalWindowIntegral shell state

    terminalMajorantMeaning :
      (shell : Nat) → (state : State) →
      Young.l1TimesSupBound (terminalConvolution shell state)
      ≡ Multiplier.euclideanInverseTransformL1Norm kernelTheorem
          * hardTerminalWindowIntegral shell state

    SmoothLowPassFactorsThroughHardNext : Set stateLevel
    smoothLowPassFactorsThroughHardNext :
      SmoothLowPassFactorsThroughHardNext

open FinitePeriodicMultiplierInputs public

gradientYoungEstimate :
  ∀ {stateLevel pointLevel}
    {State : Set stateLevel}
    {TorusPoint : Set pointLevel} →
  (inputs : FinitePeriodicMultiplierInputs State TorusPoint) →
  (shell : Nat) → (state : State) →
  smoothGradientInfinity inputs shell state
  ≤ Multiplier.euclideanInverseTransformL1Norm (kernelTheorem inputs)
      * hardGradientInfinity inputs shell state
gradientYoungEstimate inputs shell state =
  subst
    (λ upper → smoothGradientInfinity inputs shell state ≤ upper)
    (gradientMajorantMeaning inputs shell state)
    (subst
      (λ lower →
        lower ≤ Young.l1TimesSupBound (gradientConvolution inputs shell state))
      (gradientSignedSumMeaning inputs shell state)
      (Young.finiteConvolutionUpper (gradientConvolution inputs shell state)))

terminalYoungEstimate :
  ∀ {stateLevel pointLevel}
    {State : Set stateLevel}
    {TorusPoint : Set pointLevel} →
  (inputs : FinitePeriodicMultiplierInputs State TorusPoint) →
  (shell : Nat) → (state : State) →
  smoothTerminalWindowIntegral inputs shell state
  ≤ Multiplier.euclideanInverseTransformL1Norm (kernelTheorem inputs)
      * hardTerminalWindowIntegral inputs shell state
terminalYoungEstimate inputs shell state =
  subst
    (λ upper → smoothTerminalWindowIntegral inputs shell state ≤ upper)
    (terminalMajorantMeaning inputs shell state)
    (subst
      (λ lower →
        lower ≤ Young.l1TimesSupBound (terminalConvolution inputs shell state))
      (terminalSignedSumMeaning inputs shell state)
      (Young.finiteConvolutionUpper (terminalConvolution inputs shell state)))

finitePeriodicMultiplierRealization :
  ∀ {stateLevel pointLevel}
    {State : Set stateLevel}
    {TorusPoint : Set pointLevel} →
  FinitePeriodicMultiplierInputs State TorusPoint →
  Multiplier.CanonicalLuoMultiplierRealization State TorusPoint
finitePeriodicMultiplierRealization inputs = record
  { kernelTheorem = kernelTheorem inputs
  ; hardGradientInfinity = hardGradientInfinity inputs
  ; smoothGradientInfinity = smoothGradientInfinity inputs
  ; hardTerminalWindowIntegral = hardTerminalWindowIntegral inputs
  ; smoothTerminalWindowIntegral = smoothTerminalWindowIntegral inputs
  ; hardGradientNonnegative = hardGradientNonnegative inputs
  ; smoothGradientNonnegative = smoothGradientNonnegative inputs
  ; hardTerminalIntegralNonnegative = hardTerminalIntegralNonnegative inputs
  ; smoothTerminalIntegralNonnegative = smoothTerminalIntegralNonnegative inputs
  ; smoothGradientYoungEstimate = gradientYoungEstimate inputs
  ; smoothTerminalWindowYoungEstimate = terminalYoungEstimate inputs
  ; SmoothLowPassFactorsThroughHardNext =
      SmoothLowPassFactorsThroughHardNext inputs
  ; smoothLowPassFactorsThroughHardNext =
      smoothLowPassFactorsThroughHardNext inputs
  }

finitePeriodicMultiplierReducerClosed : Bool
finitePeriodicMultiplierReducerClosed = true

smoothGradientAndTerminalYoungDerivedFromFiniteReceipts : Bool
smoothGradientAndTerminalYoungDerivedFromFiniteReceipts = true

finitePeriodicMultiplierReducerClosedIsTrue :
  finitePeriodicMultiplierReducerClosed ≡ true
finitePeriodicMultiplierReducerClosedIsTrue = refl

smoothGradientAndTerminalYoungDerivedFromFiniteReceiptsIsTrue :
  smoothGradientAndTerminalYoungDerivedFromFiniteReceipts ≡ true
smoothGradientAndTerminalYoungDerivedFromFiniteReceiptsIsTrue = refl
