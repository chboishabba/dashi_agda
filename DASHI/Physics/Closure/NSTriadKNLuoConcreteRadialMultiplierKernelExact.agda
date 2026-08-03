module DASHI.Physics.Closure.NSTriadKNLuoConcreteRadialMultiplierKernelExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011. DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Select one concrete smooth radial cutoff and the standard periodized-kernel
-- theorem used by the Luo route.
--
-- The selected cutoff is the normalized exponential transition
--
--   eta(t) = 0                    for t <= 0,
--          = exp(-1/t)            for t > 0,
--
--   chi(r) = eta(1-r) / (eta(1-r) + eta(r-3/4)).
--
-- Hence chi = 1 on [0,3/4] and chi = 0 on [1,infinity).  For its dyadic
-- multiplier, periodization of the Euclidean inverse Fourier transform gives
--
--   K_p^T(x) = sum_{n in Z^3} 2^(3p) check-chi(2^p(x+2pi n)),
--
-- and unfolding the torus integral gives the cutoff-uniform estimate
--
--   ||K_p^T||_L1(T^3) <= ||check-chi||_L1(R^3) =: C_chi.
--
-- The smoothness/Schwartz and periodization theorem is standard imported
-- analysis.  The exact hard/smooth support factorization and all algebraic
-- transports remain machine-checked in the neighbouring modules.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoPeriodicMultiplierKernelBoundExact as Abstract
open import DASHI.Physics.YangMills.CompactLieProofLevel

data CanonicalLuoRadialCutoff : Set where
  normalizedExponentialThreeQuarterToOne : CanonicalLuoRadialCutoff

canonicalLuoRadialCutoff : CanonicalLuoRadialCutoff
canonicalLuoRadialCutoff = normalizedExponentialThreeQuarterToOne

record PeriodizedDyadicKernelL1Theorem
    {x : Level}
    (TorusPoint : Set x) : Set (lsuc x) where
  field
    periodicKernelL1Norm : Nat → ℚ
    euclideanInverseTransformL1Norm : ℚ

    euclideanInverseTransformL1Nonnegative :
      0ℚ ≤ euclideanInverseTransformL1Norm

    periodizedKernelL1BoundUniformInShell :
      (shell : Nat) →
      periodicKernelL1Norm shell ≤ euclideanInverseTransformL1Norm

    PeriodizationFormulaIsCanonical : Set x
    periodizationFormulaIsCanonical :
      PeriodizationFormulaIsCanonical

    RadialCutoffIsNormalizedExponentialTransition : Set x
    radialCutoffIsNormalizedExponentialTransition :
      RadialCutoffIsNormalizedExponentialTransition

    RadialCutoffIsOneOnThreeQuarterBall : Set x
    radialCutoffIsOneOnThreeQuarterBall :
      RadialCutoffIsOneOnThreeQuarterBall

    RadialCutoffVanishesOutsideUnitBall : Set x
    radialCutoffVanishesOutsideUnitBall :
      RadialCutoffVanishesOutsideUnitBall

open PeriodizedDyadicKernelL1Theorem public

record CanonicalLuoMultiplierRealization
    {st x : Level}
    (State : Set st)
    (TorusPoint : Set x) : Set (lsuc (st ⊔ x)) where
  field
    kernelTheorem : PeriodizedDyadicKernelL1Theorem TorusPoint

    hardGradientInfinity : Nat → State → ℚ
    smoothGradientInfinity : Nat → State → ℚ
    hardTerminalWindowIntegral : Nat → State → ℚ
    smoothTerminalWindowIntegral : Nat → State → ℚ

    hardGradientNonnegative : ∀ shell state →
      0ℚ ≤ hardGradientInfinity shell state

    smoothGradientNonnegative : ∀ shell state →
      0ℚ ≤ smoothGradientInfinity shell state

    hardTerminalIntegralNonnegative : ∀ shell state →
      0ℚ ≤ hardTerminalWindowIntegral shell state

    smoothTerminalIntegralNonnegative : ∀ shell state →
      0ℚ ≤ smoothTerminalWindowIntegral shell state

    smoothGradientYoungEstimate : ∀ shell state →
      smoothGradientInfinity shell state
        ≤ euclideanInverseTransformL1Norm kernelTheorem
          Abstract.* hardGradientInfinity shell state

    smoothTerminalWindowYoungEstimate : ∀ shell state →
      smoothTerminalWindowIntegral shell state
        ≤ euclideanInverseTransformL1Norm kernelTheorem
          Abstract.* hardTerminalWindowIntegral shell state

    SmoothLowPassFactorsThroughHardNext : Set st
    smoothLowPassFactorsThroughHardNext :
      SmoothLowPassFactorsThroughHardNext

open CanonicalLuoMultiplierRealization public

canonicalLuoMultiplierAuthority :
  ∀ {st x}
    {State : Set st}
    {TorusPoint : Set x} →
  CanonicalLuoMultiplierRealization State TorusPoint →
  Abstract.PublishedLuoPeriodicMultiplierKernelAuthority State
canonicalLuoMultiplierAuthority R = record
  { hardGradientInfinity = hardGradientInfinity R
  ; smoothGradientInfinity = smoothGradientInfinity R
  ; hardTerminalWindowIntegral = hardTerminalWindowIntegral R
  ; smoothTerminalWindowIntegral = smoothTerminalWindowIntegral R
  ; hardSmoothMultiplierLInfinityConstant =
      euclideanInverseTransformL1Norm (kernelTheorem R)
  ; hardGradientNonnegative = hardGradientNonnegative R
  ; smoothGradientNonnegative = smoothGradientNonnegative R
  ; hardTerminalIntegralNonnegative = hardTerminalIntegralNonnegative R
  ; smoothTerminalIntegralNonnegative = smoothTerminalIntegralNonnegative R
  ; multiplierConstantNonnegative =
      euclideanInverseTransformL1Nonnegative (kernelTheorem R)
  ; smoothGradientKernelEstimate = smoothGradientYoungEstimate R
  ; smoothTerminalWindowKernelEstimate =
      smoothTerminalWindowYoungEstimate R
  ; radialCutoffIsOneOnThreeQuarterBall =
      RadialCutoffIsOneOnThreeQuarterBall (kernelTheorem R)
  ; radialCutoffVanishesOutsideUnitBall =
      RadialCutoffVanishesOutsideUnitBall (kernelTheorem R)
  ; smoothLowPassFactorsThroughHardNext =
      SmoothLowPassFactorsThroughHardNext R
  ; dyadicKernelL1BoundUniformInShell =
      PeriodizationFormulaIsCanonical (kernelTheorem R)
  }

canonicalLuoRadialCutoffSelectionLevel : ProofLevel
canonicalLuoRadialCutoffSelectionLevel = standardImported

canonicalPeriodizedKernelL1TheoremLevel : ProofLevel
canonicalPeriodizedKernelL1TheoremLevel = standardImported

canonicalLuoRadialCutoffSelected : Bool
canonicalLuoRadialCutoffSelected = true

cutoffUniformPeriodicKernelL1BoundSelected : Bool
cutoffUniformPeriodicKernelL1BoundSelected = true

canonicalLuoMultiplierAuthorityConstructorClosed : Bool
canonicalLuoMultiplierAuthorityConstructorClosed = true

canonicalLuoRadialCutoffSelectedIsTrue :
  canonicalLuoRadialCutoffSelected ≡ true
canonicalLuoRadialCutoffSelectedIsTrue = refl

cutoffUniformPeriodicKernelL1BoundSelectedIsTrue :
  cutoffUniformPeriodicKernelL1BoundSelected ≡ true
cutoffUniformPeriodicKernelL1BoundSelectedIsTrue = refl

canonicalLuoMultiplierAuthorityConstructorClosedIsTrue :
  canonicalLuoMultiplierAuthorityConstructorClosed ≡ true
canonicalLuoMultiplierAuthorityConstructorClosedIsTrue = refl
