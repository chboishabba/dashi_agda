{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanHeatDoobJointRowCCompilerRound252Exact where

------------------------------------------------------------------------
-- ROUND252 / ONE JOINT COVARIANCE PRODUCER -> TEMPORAL + SPATIAL ROW-C INPUTS
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanThreeHalvesMetricWeightExact as Metric
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanRootedKPToExponentialWeightedHessianExact as Hess
import DASHI.Physics.YangMills.BalabanHeatDoobGradientCovarianceMarkedCauchyExact as Cov
import DASHI.Physics.YangMills.BalabanHeatDoobJointGradientCovarianceRound251Exact as Joint
import DASHI.Physics.YangMills.BalabanHeatDoobHessianCovarianceDebtExact as Temporal
import DASHI.Physics.YangMills.BalabanHeatDoobWeightedGeneratorCovarianceExact as Spatial

record JointHeatDoobRowCInputs
    (Scale Volume Root Site : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    covariance : Joint.JointHeatDoobFirstGradientCovariance Site

    -- Temporal/static side of the exact log-heat Hessian split.
    staticHessianDebt actualNegativeHessianDebt : Nat → ℚ
    staticHessianDebtNonnegative : ∀ depth → 0ℚ ≤ staticHessianDebt depth
    actualNegativeHessianDebtNonnegative : ∀ depth →
      0ℚ ≤ actualNegativeHessianDebt depth

    heatDoobTemporalSplit : ∀ depth →
      actualNegativeHessianDebt depth
      ≤ staticHessianDebt depth + Joint.temporalCovarianceDebt covariance depth

    staticTemporalBelowMarkedHessian : ∀ depth →
      staticHessianDebt depth
      ≤ Shared.hessianInfluenceShell shared scale volume root depth

    -- Spatial/static side of the same log-heat derivative generator.
    dynamicInfluence staticInfluence : Site → Site → ℚ
    dynamicInfluenceNonnegative : ∀ x y → 0ℚ ≤ dynamicInfluence x y
    staticInfluenceNonnegative : ∀ x y → 0ℚ ≤ staticInfluence x y

    heatDoobSpatialSplit : ∀ x y →
      dynamicInfluence x y
      ≤ staticInfluence x y
          + Joint.spatialCovarianceInfluence covariance x y

    rowDepth : Site → Nat

    staticSpatialRowIsMarkedHessianPartial : ∀ x →
      Sums.sumRational (Joint.sites covariance)
        (λ y → Metric.metricWeight (Joint.metric covariance) x y
          * staticInfluence x y)
      ≡ Hess.weightedHessianPartial
          (Shared.hessianWeightedControl shared)
          scale volume root (rowDepth x)

open JointHeatDoobRowCInputs public

asTemporalHeatDoobDebt :
  ∀ {Scale Volume Root Site} →
  JointHeatDoobRowCInputs Scale Volume Root Site →
  Temporal.HeatDoobHessianCovarianceDebt Scale Volume Root
asTemporalHeatDoobDebt dataSet =
  let cov = covariance dataSet
      temporal = Joint.asTemporalGradientCovariance cov
  in record
    { Temporal.HeatDoobHessianCovarianceDebt.shared = shared dataSet
    ; Temporal.HeatDoobHessianCovarianceDebt.scale = scale dataSet
    ; Temporal.HeatDoobHessianCovarianceDebt.volume = volume dataSet
    ; Temporal.HeatDoobHessianCovarianceDebt.root = root dataSet
    ; Temporal.HeatDoobHessianCovarianceDebt.staticHessianDebt =
        staticHessianDebt dataSet
    ; Temporal.HeatDoobHessianCovarianceDebt.covarianceDebt =
        Joint.temporalCovarianceDebt cov
    ; Temporal.HeatDoobHessianCovarianceDebt.actualNegativeHessianDebt =
        actualNegativeHessianDebt dataSet
    ; Temporal.HeatDoobHessianCovarianceDebt.staticNonnegative =
        staticHessianDebtNonnegative dataSet
    ; Temporal.HeatDoobHessianCovarianceDebt.covarianceNonnegative =
        Joint.temporalCovarianceDebtNonnegative cov
    ; Temporal.HeatDoobHessianCovarianceDebt.actualNonnegative =
        actualNegativeHessianDebtNonnegative dataSet
    ; Temporal.HeatDoobHessianCovarianceDebt.heatDoobSplit =
        heatDoobTemporalSplit dataSet
    ; Temporal.HeatDoobHessianCovarianceDebt.staticBelowMarkedHessian =
        staticTemporalBelowMarkedHessian dataSet
    ; Temporal.HeatDoobHessianCovarianceDebt.covarianceAmplitude =
        Cov.temporalCovarianceAmplitude temporal
    ; Temporal.HeatDoobHessianCovarianceDebt.covarianceAmplitudeNonnegative =
        Cov.temporalCovarianceAmplitudeNonnegative temporal
    ; Temporal.HeatDoobHessianCovarianceDebt.covarianceGeometricHalf =
        Joint.temporalCovarianceGeometricHalf cov
    }

asSpatialHeatDoobSplit :
  ∀ {Scale Volume Root Site} →
  JointHeatDoobRowCInputs Scale Volume Root Site →
  Spatial.HeatDoobWeightedGeneratorCovarianceSplit Scale Volume Root Site
asSpatialHeatDoobSplit dataSet =
  let cov = covariance dataSet
      spatial = Joint.asSpatialGradientCovariance cov
  in record
    { Spatial.HeatDoobWeightedGeneratorCovarianceSplit.shared = shared dataSet
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.scale = scale dataSet
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.volume = volume dataSet
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.root = root dataSet
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.sites = Joint.sites cov
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.metric = Joint.metric cov
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.dynamicInfluence =
        dynamicInfluence dataSet
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.staticInfluence =
        staticInfluence dataSet
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.covarianceInfluence =
        Joint.spatialCovarianceInfluence cov
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.dynamicNonnegative =
        dynamicInfluenceNonnegative dataSet
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.staticNonnegative =
        staticInfluenceNonnegative dataSet
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.covarianceNonnegative =
        Joint.spatialCovarianceInfluenceNonnegative cov
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.generatorSplit =
        heatDoobSpatialSplit dataSet
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.rowDepth = rowDepth dataSet
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.staticRowIsMarkedHessianPartial =
        staticSpatialRowIsMarkedHessianPartial dataSet
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.covarianceRowMass =
        Cov.spatialCovarianceRowMass spatial
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.covarianceRowMassNonnegative =
        Cov.spatialCovarianceRowMassNonnegative spatial
    ; Spatial.HeatDoobWeightedGeneratorCovarianceSplit.covarianceWeightedRowBound =
        Joint.spatialCovarianceWeightedRowBound cov
    }

jointRowCTemporalCompilerLevel : ProofLevel
jointRowCTemporalCompilerLevel = machineChecked

jointRowCSpatialCompilerLevel : ProofLevel
jointRowCSpatialCompilerLevel = machineChecked

-- The stochastic covariance estimate is one shared physical/source leaf after
-- this compiler.  The remaining non-stochastic Row-C work is the literal
-- Heat/Doob static/dynamic split and identification of the static response with
-- the SAME CMP116 hessian mark in temporal and spatial projections.
literalJointHeatDoobRowCInputsLevel : ProofLevel
literalJointHeatDoobRowCInputsLevel = conditional
