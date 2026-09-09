{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanHeatDoobJointGradientCovarianceRound251Exact where

------------------------------------------------------------------------
-- ROUND251 / ONE FIRST-GRADIENT COVARIANCE PRODUCER FEEDS BOTH ROW-C LANES
--
-- The temporal Heat/Doob curvature debt and the spatial weighted-generator debt
-- are two projections of the same covariance-of-gradients mechanism.  The
-- existing marked-Cauchy compiler already proves both projections from:
--
--   * one localized first-gradient response;
--   * one uniform companion-gradient bound;
--   * the standard bounded covariance inequality.
--
-- This owner makes the shared source object explicit so Row C does not charge
-- two unrelated physical covariance theorems.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanThreeHalvesMetricWeightExact as Metric
import DASHI.Physics.YangMills.BalabanHeatDoobGradientCovarianceMarkedCauchyExact as Cov

record JointHeatDoobFirstGradientCovariance (Site : Set) : Set₁ where
  field
    sites : List Site
    metric : Metric.NatMetricTriangle Site

    -- Temporal/RG-depth projection of the same localized first-gradient response.
    localizedGradientShell : Nat → ℚ
    localizedGradientShellNonnegative : ∀ depth →
      0ℚ ≤ localizedGradientShell depth
    gradientAmplitude : ℚ
    gradientAmplitudeNonnegative : 0ℚ ≤ gradientAmplitude
    localizedGradientGeometricHalf : ∀ depth →
      localizedGradientShell depth ≤ gradientAmplitude * Geo.halfPower depth

    -- Spatial projection of the same localized first-gradient response.
    localizedGradient : Site → Site → ℚ
    localizedGradientNonnegative : ∀ x y →
      0ℚ ≤ localizedGradient x y
    gradientWeightedRowMass : ℚ
    gradientWeightedRowMassNonnegative : 0ℚ ≤ gradientWeightedRowMass
    gradientWeightedRowBound : ∀ x →
      Sums.sumRational sites
        (λ y → Metric.metricWeight metric x y * localizedGradient x y)
      ≤ gradientWeightedRowMass

    -- One companion-gradient bound is shared by both projections because both
    -- covariance terms are evaluated on the same Heat/Doob density and common
    -- CMP116 analytic polydisc.
    companionGradientBound : ℚ
    companionGradientBoundNonnegative : 0ℚ ≤ companionGradientBound

    temporalCovarianceDebt : Nat → ℚ
    temporalCovarianceDebtNonnegative : ∀ depth →
      0ℚ ≤ temporalCovarianceDebt depth
    temporalCovarianceBelowTwoProducts : ∀ depth →
      temporalCovarianceDebt depth
      ≤ Cov.two * (localizedGradientShell depth * companionGradientBound)

    spatialCovarianceInfluence : Site → Site → ℚ
    spatialCovarianceInfluenceNonnegative : ∀ x y →
      0ℚ ≤ spatialCovarianceInfluence x y
    spatialCovarianceBelowTwoProducts : ∀ x y →
      spatialCovarianceInfluence x y
      ≤ Cov.two * (localizedGradient x y * companionGradientBound)

open JointHeatDoobFirstGradientCovariance public

asTemporalGradientCovariance :
  ∀ {Site} → JointHeatDoobFirstGradientCovariance Site →
  Cov.HeatDoobTemporalGradientCovariance
asTemporalGradientCovariance dataSet = record
  { Cov.HeatDoobTemporalGradientCovariance.localizedGradientShell =
      localizedGradientShell dataSet
  ; Cov.HeatDoobTemporalGradientCovariance.localizedGradientNonnegative =
      localizedGradientShellNonnegative dataSet
  ; Cov.HeatDoobTemporalGradientCovariance.gradientAmplitude =
      gradientAmplitude dataSet
  ; Cov.HeatDoobTemporalGradientCovariance.gradientAmplitudeNonnegative =
      gradientAmplitudeNonnegative dataSet
  ; Cov.HeatDoobTemporalGradientCovariance.localizedGradientGeometricHalf =
      localizedGradientGeometricHalf dataSet
  ; Cov.HeatDoobTemporalGradientCovariance.companionGradientBound =
      companionGradientBound dataSet
  ; Cov.HeatDoobTemporalGradientCovariance.companionGradientBoundNonnegative =
      companionGradientBoundNonnegative dataSet
  ; Cov.HeatDoobTemporalGradientCovariance.covarianceDebt =
      temporalCovarianceDebt dataSet
  ; Cov.HeatDoobTemporalGradientCovariance.covarianceDebtNonnegative =
      temporalCovarianceDebtNonnegative dataSet
  ; Cov.HeatDoobTemporalGradientCovariance.covarianceBelowTwoGradientProducts =
      temporalCovarianceBelowTwoProducts dataSet
  }

asSpatialGradientCovariance :
  ∀ {Site} (dataSet : JointHeatDoobFirstGradientCovariance Site) →
  Cov.HeatDoobSpatialGradientCovariance Site
asSpatialGradientCovariance dataSet = record
  { Cov.HeatDoobSpatialGradientCovariance.sites = sites dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.metric = metric dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.localizedGradient =
      localizedGradient dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.covarianceInfluence =
      spatialCovarianceInfluence dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.localizedGradientNonnegative =
      localizedGradientNonnegative dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.covarianceInfluenceNonnegative =
      spatialCovarianceInfluenceNonnegative dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.companionGradientBound =
      companionGradientBound dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.companionGradientBoundNonnegative =
      companionGradientBoundNonnegative dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.gradientWeightedRowMass =
      gradientWeightedRowMass dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.gradientWeightedRowMassNonnegative =
      gradientWeightedRowMassNonnegative dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.gradientWeightedRowBound =
      gradientWeightedRowBound dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.covarianceBelowTwoGradientProducts =
      spatialCovarianceBelowTwoProducts dataSet
  }

temporalCovarianceGeometricHalf :
  ∀ {Site} (dataSet : JointHeatDoobFirstGradientCovariance Site) depth →
  temporalCovarianceDebt dataSet depth
  ≤ Cov.temporalCovarianceAmplitude (asTemporalGradientCovariance dataSet)
      * Geo.halfPower depth
temporalCovarianceGeometricHalf dataSet =
  Cov.temporalCovarianceGeometricHalf (asTemporalGradientCovariance dataSet)

spatialCovarianceWeightedRowBound :
  ∀ {Site} (dataSet : JointHeatDoobFirstGradientCovariance Site) x →
  Sums.sumRational (sites dataSet)
    (λ y → Metric.metricWeight (metric dataSet) x y
      * spatialCovarianceInfluence dataSet x y)
  ≤ Cov.spatialCovarianceRowMass (asSpatialGradientCovariance dataSet)
spatialCovarianceWeightedRowBound dataSet =
  Cov.covarianceWeightedRowBound (asSpatialGradientCovariance dataSet)

jointHeatDoobGradientCovarianceCompilerLevel : ProofLevel
jointHeatDoobGradientCovarianceCompilerLevel = machineChecked

-- Single Row-C stochastic/source leaf after the joint compilation: instantiate
-- the literal first-gradient localized response and companion-gradient bound on
-- the SAME CMP116 common analytic polydisc / Heat-Doob density, with its temporal
-- and spatial projections.  The covariance inequality and both summations are
-- already compiler/standard-analysis consequences.
literalJointCMP116HeatDoobFirstGradientInstantiationLevel : ProofLevel
literalJointCMP116HeatDoobFirstGradientInstantiationLevel =
  Cov.literalCMP116FirstGradientHeatDoobCovarianceInstantiationLevel
