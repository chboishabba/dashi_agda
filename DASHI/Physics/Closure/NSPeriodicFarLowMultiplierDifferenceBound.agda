module DASHI.Physics.Closure.NSPeriodicFarLowMultiplierDifferenceBound where

open import Agda.Primitive using (Level; lsuc)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; _*ℝ_
  ; _≤ℝ_
  ; ≤ℝ-refl
  ; ≤ℝ-trans
  ; mulMonotoneNonnegative
  )
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Mean-value reduction for the literal multiplier difference.
--
-- The exact kernel remains owned by NSPeriodicFarLowMultiplierDifferenceKernel.
-- This module proves that once the profile-gradient estimate and low-support
-- radius are supplied separately, their product yields the scale-separation
-- factor.  No absolute Schur conclusion is built into the pointwise theorem.
------------------------------------------------------------------------

record PointwiseMultiplierDifferenceInputs
    {ℓ : Level}
    (Mode : Set ℓ) : Set (lsuc ℓ) where
  field
    absoluteDifference : Mode → Mode → ℝ
    latticeDistance : Mode → Mode → ℝ

    gradientScale : ℝ
    lowRadius : ℝ
    separationFactor : ℝ
    meanValueConstant : ℝ

    absoluteDifferenceNonnegative : ∀ q p →
      0ℝ ≤ℝ absoluteDifference q p

    gradientScaleNonnegative : 0ℝ ≤ℝ gradientScale
    latticeDistanceNonnegative : ∀ q p →
      0ℝ ≤ℝ latticeDistance q p

    meanValueStep : ∀ q p →
      absoluteDifference q p
      ≤ℝ gradientScale *ℝ latticeDistance q p

    lowSupportRadius : ∀ q p →
      latticeDistance q p ≤ℝ lowRadius

    scaledLowRadiusFitsSeparation :
      gradientScale *ℝ lowRadius
      ≤ℝ meanValueConstant *ℝ separationFactor

open PointwiseMultiplierDifferenceInputs public

multiplierDifferenceFitsSeparation :
  ∀ {ℓ} {Mode : Set ℓ} →
  (I : PointwiseMultiplierDifferenceInputs Mode) →
  ∀ q p →
  absoluteDifference I q p
  ≤ℝ meanValueConstant I *ℝ separationFactor I
multiplierDifferenceFitsSeparation I q p =
  ≤ℝ-trans
    (meanValueStep I q p)
    (≤ℝ-trans
      gradientTimesDistanceBelowGradientTimesLowRadius
      (scaledLowRadiusFitsSeparation I))
  where
  gradientTimesDistanceBelowGradientTimesLowRadius :
    gradientScale I *ℝ latticeDistance I q p
    ≤ℝ gradientScale I *ℝ lowRadius I
  gradientTimesDistanceBelowGradientTimesLowRadius =
    mulMonotoneNonnegative
      (gradientScaleNonnegative I)
      ≤ℝ-refl
      (latticeDistanceNonnegative I q p)
      (lowSupportRadius I q p)

------------------------------------------------------------------------
-- Pointwise absolute-kernel majorisation.  This still does not assert that the
-- row and column folds are cutoff-uniform; it only transports the multiplier
-- gain through a nonnegative bilinear-symbol majorant.
------------------------------------------------------------------------

record AbsoluteDifferenceKernelInputs
    {ℓ : Level}
    (Mode : Set ℓ) : Set (lsuc ℓ) where
  field
    multiplierInputs : PointwiseMultiplierDifferenceInputs Mode
    symbolMajorant : Mode → Mode → Mode → ℝ
    symbolMajorantNonnegative : ∀ k p q →
      0ℝ ≤ℝ symbolMajorant k p q

open AbsoluteDifferenceKernelInputs public

absoluteDifferenceKernelValue :
  ∀ {ℓ} {Mode : Set ℓ} →
  AbsoluteDifferenceKernelInputs Mode →
  Mode → Mode → Mode → ℝ
absoluteDifferenceKernelValue I k p q =
  absoluteDifference (multiplierInputs I) q p
  *ℝ symbolMajorant I k p q

separatedKernelMajorant :
  ∀ {ℓ} {Mode : Set ℓ} →
  AbsoluteDifferenceKernelInputs Mode →
  Mode → Mode → Mode → ℝ
separatedKernelMajorant I k p q =
  (meanValueConstant (multiplierInputs I)
    *ℝ separationFactor (multiplierInputs I))
  *ℝ symbolMajorant I k p q

absoluteDifferenceKernelPointwiseBound :
  ∀ {ℓ} {Mode : Set ℓ} →
  (I : AbsoluteDifferenceKernelInputs Mode) →
  ∀ k p q →
  absoluteDifferenceKernelValue I k p q
  ≤ℝ separatedKernelMajorant I k p q
absoluteDifferenceKernelPointwiseBound I k p q =
  mulMonotoneNonnegative
    (absoluteDifferenceNonnegative (multiplierInputs I) q p)
    (multiplierDifferenceFitsSeparation (multiplierInputs I) q p)
    (symbolMajorantNonnegative I k p q)
    ≤ℝ-refl

farLowMultiplierDifferenceReductionLevel : ProofLevel
farLowMultiplierDifferenceReductionLevel = machineChecked

concreteSmoothDyadicProfileGradientLevel : ProofLevel
concreteSmoothDyadicProfileGradientLevel = conditional

cutoffUniformDifferenceKernelSchurLevel : ProofLevel
cutoffUniformDifferenceKernelSchurLevel = conditional
