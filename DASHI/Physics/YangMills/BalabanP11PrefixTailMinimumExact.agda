module DASHI.Physics.YangMills.BalabanP11PrefixTailMinimumExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I",
-- Communications in Mathematical Physics 109 (1987).
-- DOI: 10.1007/BF01215223.
--
-- PURPOSE
--
-- Round seven reduced P11 to one uniform lower bound p0Minimum <= p0(k).
-- This module performs the next useful reduction: the all-scale lower bound is
-- assembled from a finite-prefix estimate and an asymptotic-tail estimate.
-- Thus the remaining analytic work may use different arguments in the strong-
-- coupling startup regime and the asymptotically free regime without
-- reintroducing a scale-by-scale absorption postulate.
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _<_; _≤_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _≤ℝ_
  ; _*ℝ_
  ; 0ℝ
  )
import DASHI.Physics.YangMills.BalabanLargeFieldSuppression as LargeField
import DASHI.Physics.YangMills.BalabanP11UniformAbsorptionReductionExact as P11
open P11.P11UniformAbsorptionInputs using
  ( p0Minimum
  ; p0MinimumNonnegative
  ; cAbsNonnegative
  ; entropyThresholdPaidAtMinimum
  ; p0MinimumBelowEveryScale
  )
open import DASHI.Physics.YangMills.CompactLieProofLevel

record P11PrefixTailMinimumInputs : Set₁ where
  field
    transitionScale : ℕ

    prefixMinimum : ℝ
    tailMinimum : ℝ
    globalMinimum : ℝ

    scaleIsPrefixOrTail :
      ∀ scale →
      (scale < transitionScale) ⊎ (transitionScale ≤ scale)

    globalMinimumBelowPrefixMinimum :
      globalMinimum ≤ℝ prefixMinimum

    globalMinimumBelowTailMinimum :
      globalMinimum ≤ℝ tailMinimum

    prefixMinimumBelowP0 :
      ∀ scale →
      scale < transitionScale →
      prefixMinimum ≤ℝ LargeField.p0 scale

    tailMinimumBelowP0 :
      ∀ scale →
      transitionScale ≤ scale →
      tailMinimum ≤ℝ LargeField.p0 scale

    globalMinimumNonnegative :
      0ℝ ≤ℝ globalMinimum

    globalCAbsNonnegative :
      0ℝ ≤ℝ LargeField.c-abs

    entropyThresholdPaidAtGlobalMinimum :
      P11.p11EntropyThreshold ≤ℝ
        (LargeField.c-abs *ℝ globalMinimum)

open P11PrefixTailMinimumInputs public

proveGlobalMinimumBelowEveryScale :
  (inputs : P11PrefixTailMinimumInputs) →
  ∀ scale →
  globalMinimum inputs ≤ℝ LargeField.p0 scale
proveGlobalMinimumBelowEveryScale inputs scale
  with scaleIsPrefixOrTail inputs scale
... | inj₁ prefix =
  LargeField.OrderedRealKernel.≤-trans
    LargeField.currentOrderedRealKernel
    (globalMinimum inputs)
    (prefixMinimum inputs)
    (LargeField.p0 scale)
    (globalMinimumBelowPrefixMinimum inputs)
    (prefixMinimumBelowP0 inputs scale prefix)
... | inj₂ tail =
  LargeField.OrderedRealKernel.≤-trans
    LargeField.currentOrderedRealKernel
    (globalMinimum inputs)
    (tailMinimum inputs)
    (LargeField.p0 scale)
    (globalMinimumBelowTailMinimum inputs)
    (tailMinimumBelowP0 inputs scale tail)

p11UniformInputsFromPrefixTail :
  P11PrefixTailMinimumInputs →
  P11.P11UniformAbsorptionInputs
p11UniformInputsFromPrefixTail inputs = record
  { p0Minimum = globalMinimum inputs
  ; p0MinimumNonnegative = globalMinimumNonnegative inputs
  ; cAbsNonnegative = globalCAbsNonnegative inputs
  ; entropyThresholdPaidAtMinimum =
      entropyThresholdPaidAtGlobalMinimum inputs
  ; p0MinimumBelowEveryScale =
      proveGlobalMinimumBelowEveryScale inputs
  }

p11AbsorptionConditionFromPrefixTail :
  P11PrefixTailMinimumInputs →
  LargeField.ImportedAbsorptionCondition
p11AbsorptionConditionFromPrefixTail inputs =
  P11.p11AbsorptionConditionFromUniformMinimum
    (p11UniformInputsFromPrefixTail inputs)

p11PrefixTailMinimumReductionLevel : ProofLevel
p11PrefixTailMinimumReductionLevel = machineChecked

p11PhysicalPrefixAndTailBoundsLevel : ProofLevel
p11PhysicalPrefixAndTailBoundsLevel = conditional
