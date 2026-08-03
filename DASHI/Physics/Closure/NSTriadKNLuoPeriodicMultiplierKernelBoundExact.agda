module DASHI.Physics.Closure.NSTriadKNLuoPeriodicMultiplierKernelBoundExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal/year: Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011. DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- State the standard periodic multiplier theorem in exactly the form consumed
-- by the Luo route.  A fixed smooth radial cutoff and its dyadic dilates have
-- a scale-uniform periodic convolution-kernel L1 bound C_chi.  Young's
-- inequality then compares the smooth low-pass gradient with the already
-- differentiated hard low-pass gradient, with no derivative Bernstein or
-- L2-to-L-infinity factor.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNHardSmoothLittlewoodPaleyTransferExact as Transfer
open import DASHI.Physics.YangMills.CompactLieProofLevel

record PublishedLuoPeriodicMultiplierKernelAuthority
    {st : Level}
    (State : Set st) : Set (lsuc st) where
  field
    hardGradientInfinity : Nat → State → ℚ
    smoothGradientInfinity : Nat → State → ℚ

    hardTerminalWindowIntegral : Nat → State → ℚ
    smoothTerminalWindowIntegral : Nat → State → ℚ

    hardSmoothMultiplierLInfinityConstant : ℚ

    hardGradientNonnegative : ∀ shell state →
      0ℚ ≤ hardGradientInfinity shell state

    smoothGradientNonnegative : ∀ shell state →
      0ℚ ≤ smoothGradientInfinity shell state

    hardTerminalIntegralNonnegative : ∀ shell state →
      0ℚ ≤ hardTerminalWindowIntegral shell state

    smoothTerminalIntegralNonnegative : ∀ shell state →
      0ℚ ≤ smoothTerminalWindowIntegral shell state

    multiplierConstantNonnegative :
      0ℚ ≤ hardSmoothMultiplierLInfinityConstant

    smoothGradientKernelEstimate : ∀ shell state →
      smoothGradientInfinity shell state
        ≤ hardSmoothMultiplierLInfinityConstant
          * hardGradientInfinity shell state

    smoothTerminalWindowKernelEstimate : ∀ shell state →
      smoothTerminalWindowIntegral shell state
        ≤ hardSmoothMultiplierLInfinityConstant
          * hardTerminalWindowIntegral shell state

    radialCutoffIsOneOnThreeQuarterBall : Set st
    radialCutoffVanishesOutsideUnitBall : Set st
    smoothLowPassFactorsThroughHardNext : Set st
    dyadicKernelL1BoundUniformInShell : Set st

open PublishedLuoPeriodicMultiplierKernelAuthority public

hardSmoothGradientComparisonFromKernelAuthority :
  ∀ {st} {State : Set st} →
  (A : PublishedLuoPeriodicMultiplierKernelAuthority State) →
  (shell : Nat) →
  (state : State) →
  Transfer.HardSmoothLowPassGradientComparison
hardSmoothGradientComparisonFromKernelAuthority A shell state =
  Transfer.comparison
    shell
    (hardGradientInfinity A shell state)
    (smoothGradientInfinity A shell state)
    (hardSmoothMultiplierLInfinityConstant A)
    (hardGradientNonnegative A shell state)
    (smoothGradientNonnegative A shell state)
    (multiplierConstantNonnegative A)
    (smoothGradientKernelEstimate A shell state)

record LuoTerminalWindowBudget
    {st : Level}
    {State : Set st}
    (A : PublishedLuoPeriodicMultiplierKernelAuthority State)
    (shell : Nat)
    (state : State) : Set where
  field
    hardBudget : ℚ
    universalThreshold : ℚ

    hardBudgetNonnegative : 0ℚ ≤ hardBudget
    universalThresholdNonnegative : 0ℚ ≤ universalThreshold

    hardIntegralBelowBudget :
      hardTerminalWindowIntegral A shell state ≤ hardBudget

    scaledBudgetBelowThreshold :
      hardSmoothMultiplierLInfinityConstant A * hardBudget
        ≤ universalThreshold

open LuoTerminalWindowBudget public

hardSmoothTerminalComparisonFromKernelAuthority :
  ∀ {st} {State : Set st} →
  (A : PublishedLuoPeriodicMultiplierKernelAuthority State) →
  (shell : Nat) →
  (state : State) →
  (B : LuoTerminalWindowBudget A shell state) →
  Transfer.HardSmoothTerminalWindowComparison
hardSmoothTerminalComparisonFromKernelAuthority A shell state B =
  Transfer.terminal-comparison
    shell
    (hardTerminalWindowIntegral A shell state)
    (smoothTerminalWindowIntegral A shell state)
    (hardBudget B)
    (universalThreshold B)
    (hardSmoothMultiplierLInfinityConstant A)
    (hardTerminalIntegralNonnegative A shell state)
    (smoothTerminalIntegralNonnegative A shell state)
    (hardBudgetNonnegative B)
    (universalThresholdNonnegative B)
    (multiplierConstantNonnegative A)
    (smoothTerminalWindowKernelEstimate A shell state)
    (hardIntegralBelowBudget B)
    (scaledBudgetBelowThreshold B)

luoSmoothCriterionFromHardBudget :
  ∀ {st} {State : Set st} →
  (A : PublishedLuoPeriodicMultiplierKernelAuthority State) →
  (shell : Nat) →
  (state : State) →
  (B : LuoTerminalWindowBudget A shell state) →
  smoothTerminalWindowIntegral A shell state
    ≤ universalThreshold B
luoSmoothCriterionFromHardBudget A shell state B =
  Transfer.hardTerminalWindowBudgetTransfersToLuoSmoothCriterion
    (hardSmoothTerminalComparisonFromKernelAuthority A shell state B)

luoPeriodicMultiplierKernelBoundLevel : ProofLevel
luoPeriodicMultiplierKernelBoundLevel = standardImported

publishedLuoPeriodicMultiplierAuthoritySurfaceConstructed : Bool
publishedLuoPeriodicMultiplierAuthoritySurfaceConstructed = true

hardSmoothTerminalCriterionTransportClosed : Bool
hardSmoothTerminalCriterionTransportClosed = true

concretePublishedLuoMultiplierAuthoritySelected : Bool
concretePublishedLuoMultiplierAuthoritySelected = false

publishedLuoPeriodicMultiplierAuthoritySurfaceConstructedIsTrue :
  publishedLuoPeriodicMultiplierAuthoritySurfaceConstructed ≡ true
publishedLuoPeriodicMultiplierAuthoritySurfaceConstructedIsTrue = refl

hardSmoothTerminalCriterionTransportClosedIsTrue :
  hardSmoothTerminalCriterionTransportClosed ≡ true
hardSmoothTerminalCriterionTransportClosedIsTrue = refl

concretePublishedLuoMultiplierAuthoritySelectedIsFalse :
  concretePublishedLuoMultiplierAuthoritySelected ≡ false
concretePublishedLuoMultiplierAuthoritySelectedIsFalse = refl
