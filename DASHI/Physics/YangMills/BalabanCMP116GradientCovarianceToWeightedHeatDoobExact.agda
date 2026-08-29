{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116GradientCovarianceToWeightedHeatDoobExact where

------------------------------------------------------------------------
-- ROUND102 B->C SPATIAL CAPSTONE
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanThreeHalvesMetricWeightExact as Metric
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanRootedKPToExponentialWeightedHessianExact as Hess
import DASHI.Physics.YangMills.BalabanHeatDoobGradientCovarianceMarkedCauchyExact as Grad
import DASHI.Physics.YangMills.BalabanHeatDoobWeightedGeneratorCovarianceExact as Heat
import DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact as Weighted
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

record CMP116GradientCovarianceWeightedHeatDoobData
    (Scale Volume Root Site : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    gradientCovariance : Grad.HeatDoobSpatialGradientCovariance Site

    dynamicInfluence staticInfluence : Site → Site → ℚ
    dynamicNonnegative : ∀ x y → 0ℚ ≤ dynamicInfluence x y
    staticNonnegative : ∀ x y → 0ℚ ≤ staticInfluence x y

    generatorSplit : ∀ x y →
      dynamicInfluence x y
      ≤ staticInfluence x y
        + Grad.covarianceInfluence gradientCovariance x y

    rowDepth : Site → Nat

    staticRowIsMarkedHessianPartial : ∀ x →
      Sums.sumRational (Grad.sites gradientCovariance)
        (λ y →
          Metric.metricWeight (Grad.metric gradientCovariance) x y
            * staticInfluence x y)
      ≡ Hess.weightedHessianPartial
          (Shared.hessianWeightedControl shared)
          scale volume root (rowDepth x)

open CMP116GradientCovarianceWeightedHeatDoobData public

asWeightedGeneratorCovarianceSplit :
  ∀ {Scale Volume Root Site} →
  CMP116GradientCovarianceWeightedHeatDoobData Scale Volume Root Site →
  Heat.HeatDoobWeightedGeneratorCovarianceSplit Scale Volume Root Site
asWeightedGeneratorCovarianceSplit dataSet = record
  { Heat.HeatDoobWeightedGeneratorCovarianceSplit.shared = shared dataSet
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.scale = scale dataSet
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.volume = volume dataSet
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.root = root dataSet
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.sites =
      Grad.sites (gradientCovariance dataSet)
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.metric =
      Grad.metric (gradientCovariance dataSet)
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.dynamicInfluence = dynamicInfluence dataSet
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.staticInfluence = staticInfluence dataSet
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.covarianceInfluence =
      Grad.covarianceInfluence (gradientCovariance dataSet)
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.dynamicNonnegative = dynamicNonnegative dataSet
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.staticNonnegative = staticNonnegative dataSet
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.covarianceNonnegative =
      Grad.covarianceInfluenceNonnegative (gradientCovariance dataSet)
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.generatorSplit = generatorSplit dataSet
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.rowDepth = rowDepth dataSet
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.staticRowIsMarkedHessianPartial =
      staticRowIsMarkedHessianPartial dataSet
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.covarianceRowMass =
      Grad.spatialCovarianceRowMass (gradientCovariance dataSet)
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.covarianceRowMassNonnegative =
      Grad.spatialCovarianceRowMassNonnegative (gradientCovariance dataSet)
  ; Heat.HeatDoobWeightedGeneratorCovarianceSplit.covarianceWeightedRowBound =
      Grad.covarianceWeightedRowBound (gradientCovariance dataSet)
  }

allDynamicWeightedPowerRowsFromCMP116Gradients :
  ∀ {Scale Volume Root Site}
    (dataSet : CMP116GradientCovarianceWeightedHeatDoobData Scale Volume Root Site)
    n x →
  Weighted.weightedPowerRow
    (Heat.asWeightedDynamicMajorant (asWeightedGeneratorCovarianceSplit dataSet)) n x
  ≤ Power.rationalPower
      (Shared.hessianAnalyticConstant (shared dataSet)
        + Grad.spatialCovarianceRowMass (gradientCovariance dataSet))
      (Agda.Builtin.Nat.suc n)
allDynamicWeightedPowerRowsFromCMP116Gradients dataSet =
  Heat.allDynamicWeightedPowerRows (asWeightedGeneratorCovarianceSplit dataSet)

cmp116GradientCovarianceToWeightedHeatDoobLevel : ProofLevel
cmp116GradientCovarianceToWeightedHeatDoobLevel = machineChecked

literalCMP116GradientHeatDoobSpatialInstantiationLevel : ProofLevel
literalCMP116GradientHeatDoobSpatialInstantiationLevel = conditional
