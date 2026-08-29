{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116FirstGradientCovarianceInstantiationRound102Exact where

------------------------------------------------------------------------
-- ROUND102 B->C: SHARED FIRST-GRADIENT CARRIER -> COVARIANCE SHELL/ROW
--
-- This removes covariance decay as an independent premise.  The hessian-mark
-- analytic shell is source-native and finite Cauchy differentiation preserves
-- its localization.  A first-gradient response below that shell therefore has
-- the already-owned 1/2 geometric decay and weighted-row constant.  Multiplying
-- by one uniform companion-gradient bound gives the genuine Heat/Doob covariance
-- debt through the standard bounded covariance inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116FirstGradientSharedMarkedExact as First
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as Geom
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanHeatDoobGradientCovarianceMarkedCauchyExact as Cov
import DASHI.Physics.YangMills.BalabanThreeHalvesMetricWeightExact as Metric
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

------------------------------------------------------------------------
-- Temporal shell instantiation
------------------------------------------------------------------------

record CMP116TemporalFirstGradientCovariance
    (Scale Volume Root : Set) : Set₁ where
  field
    firstGradient : First.CMP116FirstGradientSharedMarkedControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    companionGradientBound : ℚ
    companionGradientBoundNonnegative : 0ℚ ≤ companionGradientBound

    covarianceDebt : Nat → ℚ
    covarianceDebtNonnegative : ∀ n → 0ℚ ≤ covarianceDebt n

    covarianceBelowTwoGradientProducts : ∀ n →
      covarianceDebt n
      ≤ Cov.two *
          (First.firstGradientShell firstGradient scale volume root n
            * companionGradientBound)

open CMP116TemporalFirstGradientCovariance public

asTemporalGradientCovariance :
  ∀ {Scale Volume Root} →
  CMP116TemporalFirstGradientCovariance Scale Volume Root →
  Cov.HeatDoobTemporalGradientCovariance
asTemporalGradientCovariance dataSet = record
  { Cov.HeatDoobTemporalGradientCovariance.localizedGradientShell =
      First.firstGradientShell
        (firstGradient dataSet) (scale dataSet) (volume dataSet) (root dataSet)
  ; Cov.HeatDoobTemporalGradientCovariance.localizedGradientNonnegative =
      First.firstGradientShellNonnegative
        (firstGradient dataSet) (scale dataSet) (volume dataSet) (root dataSet)
  ; Cov.HeatDoobTemporalGradientCovariance.gradientAmplitude =
      Geom.markedBaseEnergy
        (First.shared (firstGradient dataSet)) Shared.hessianMark
  ; Cov.HeatDoobTemporalGradientCovariance.gradientAmplitudeNonnegative =
      Geom.markedBaseEnergyNonnegative
        (First.shared (firstGradient dataSet)) Shared.hessianMark
  ; Cov.HeatDoobTemporalGradientCovariance.localizedGradientGeometricHalf =
      Geom.responseGeometricHalf
        (First.shared (firstGradient dataSet))
        Shared.hessianMark
        (First.firstGradientShell (firstGradient dataSet))
        (First.firstGradientBelowHessianMarkedAnalytic (firstGradient dataSet))
        (scale dataSet) (volume dataSet) (root dataSet)
  ; Cov.HeatDoobTemporalGradientCovariance.companionGradientBound =
      companionGradientBound dataSet
  ; Cov.HeatDoobTemporalGradientCovariance.companionGradientBoundNonnegative =
      companionGradientBoundNonnegative dataSet
  ; Cov.HeatDoobTemporalGradientCovariance.covarianceDebt = covarianceDebt dataSet
  ; Cov.HeatDoobTemporalGradientCovariance.covarianceDebtNonnegative =
      covarianceDebtNonnegative dataSet
  ; Cov.HeatDoobTemporalGradientCovariance.covarianceBelowTwoGradientProducts =
      covarianceBelowTwoGradientProducts dataSet
  }

------------------------------------------------------------------------
-- Spatial row instantiation
------------------------------------------------------------------------

record CMP116SpatialFirstGradientCovariance
    (Scale Volume Root Site : Set) : Set₁ where
  field
    firstGradient : First.CMP116FirstGradientSharedMarkedControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    sites : List Site
    metric : Metric.NatMetricTriangle Site

    localizedGradient covarianceInfluence : Site → Site → ℚ
    localizedGradientNonnegative : ∀ x y → 0ℚ ≤ localizedGradient x y
    covarianceInfluenceNonnegative : ∀ x y → 0ℚ ≤ covarianceInfluence x y

    companionGradientBound : ℚ
    companionGradientBoundNonnegative : 0ℚ ≤ companionGradientBound

    rowDepth : Site → Nat

    -- Literal finite-row identification of the first derivative with the SAME
    -- CMP116 weighted marked response.
    weightedGradientRowIsMarkedPartial : ∀ x →
      Sums.sumRational sites
        (λ y → Metric.metricWeight metric x y * localizedGradient x y)
      ≡ First.firstGradientWeightedPartial
          firstGradient scale volume root (rowDepth x)

    covarianceBelowTwoGradientProducts : ∀ x y →
      covarianceInfluence x y
      ≤ Cov.two * (localizedGradient x y * companionGradientBound)

open CMP116SpatialFirstGradientCovariance public

asSpatialGradientCovariance :
  ∀ {Scale Volume Root Site} →
  CMP116SpatialFirstGradientCovariance Scale Volume Root Site →
  Cov.HeatDoobSpatialGradientCovariance Site
asSpatialGradientCovariance dataSet = record
  { Cov.HeatDoobSpatialGradientCovariance.sites = sites dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.metric = metric dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.localizedGradient = localizedGradient dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.covarianceInfluence = covarianceInfluence dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.localizedGradientNonnegative =
      localizedGradientNonnegative dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.covarianceInfluenceNonnegative =
      covarianceInfluenceNonnegative dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.companionGradientBound =
      companionGradientBound dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.companionGradientBoundNonnegative =
      companionGradientBoundNonnegative dataSet
  ; Cov.HeatDoobSpatialGradientCovariance.gradientWeightedRowMass =
      Shared.hessianAnalyticConstant (First.shared (firstGradient dataSet))
  ; Cov.HeatDoobSpatialGradientCovariance.gradientWeightedRowMassNonnegative =
      Shared.markedConstantNonnegative
        (First.shared (firstGradient dataSet)) Shared.hessianMark
  ; Cov.HeatDoobSpatialGradientCovariance.gradientWeightedRowBound =
      λ x →
        subst
          (λ left → left ≤
            Shared.hessianAnalyticConstant (First.shared (firstGradient dataSet)))
          (weightedGradientRowIsMarkedPartial dataSet x)
          (First.firstGradientWeightedPartialBelowSharedConstant
            (firstGradient dataSet)
            (scale dataSet) (volume dataSet) (root dataSet) (rowDepth dataSet x))
  ; Cov.HeatDoobSpatialGradientCovariance.covarianceBelowTwoGradientProducts =
      covarianceBelowTwoGradientProducts dataSet
  }

cmp116FirstGradientToTemporalCovarianceLevel : ProofLevel
cmp116FirstGradientToTemporalCovarianceLevel = machineChecked

cmp116FirstGradientToSpatialCovarianceLevel : ProofLevel
cmp116FirstGradientToSpatialCovarianceLevel = machineChecked

-- Remaining physical content is now exactly source/coordinate identification of
-- the first derivative and the standard conditional covariance product bound.
-- No separate covariance localization estimate remains.
literalCMP116FirstGradientHeatDoobIdentificationLevel : ProofLevel
literalCMP116FirstGradientHeatDoobIdentificationLevel = conditional
