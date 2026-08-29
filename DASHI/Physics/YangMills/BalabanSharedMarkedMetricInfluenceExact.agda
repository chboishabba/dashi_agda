{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSharedMarkedMetricInfluenceExact where

------------------------------------------------------------------------
-- ROW C SPATIAL SOURCE SURFACE AFTER BIDI REDUCTION
--
-- Combine the two preceding exact compilers:
--
--   integer metric triangle
--       -> submultiplicative weight (3/2)^distance,
--
--   one weighted generator row <= shared CMP116 Hessian constant
--       -> the same weighted bound for every positive Dyson power.
--
-- Consequently the physical source surface needs no abstract weight fields and
-- no all-power estimates.  It consists only of the literal finite site metric,
-- the absolute derivative generator, and ONE same-object weighted row bound.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanThreeHalvesMetricWeightExact as Metric
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianToWeightedInfluenceExact as Bridge
import DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact as Weighted
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

record SharedMarkedMetricInfluenceBridge
    (Scale Volume Root Site : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    sites : List Site
    metric : Metric.NatMetricTriangle Site
    influence : Site → Site → ℚ
    influenceNonnegative : ∀ x y → 0ℚ ≤ influence x y

    -- The sole analytic same-object spatial comparison.
    weightedGeneratorRowBelowSharedHessian : ∀ x →
      Sums.sumRational sites
        (λ y → Metric.metricWeight metric x y * influence x y)
      ≤ Shared.hessianAnalyticConstant shared

open SharedMarkedMetricInfluenceBridge public

asWeightedBridge :
  ∀ {Scale Volume Root Site} →
  SharedMarkedMetricInfluenceBridge Scale Volume Root Site →
  Bridge.SharedMarkedWeightedInfluenceBridge Scale Volume Root Site
asWeightedBridge dataSet = record
  { Bridge.SharedMarkedWeightedInfluenceBridge.shared = shared dataSet
  ; Bridge.SharedMarkedWeightedInfluenceBridge.scale = scale dataSet
  ; Bridge.SharedMarkedWeightedInfluenceBridge.volume = volume dataSet
  ; Bridge.SharedMarkedWeightedInfluenceBridge.root = root dataSet
  ; Bridge.SharedMarkedWeightedInfluenceBridge.sites = sites dataSet
  ; Bridge.SharedMarkedWeightedInfluenceBridge.influence = influence dataSet
  ; Bridge.SharedMarkedWeightedInfluenceBridge.weight =
      Metric.metricWeight (metric dataSet)
  ; Bridge.SharedMarkedWeightedInfluenceBridge.influenceNonnegative =
      influenceNonnegative dataSet
  ; Bridge.SharedMarkedWeightedInfluenceBridge.weightNonnegative =
      Metric.metricWeightNonnegative (metric dataSet)
  ; Bridge.SharedMarkedWeightedInfluenceBridge.weightAtLeastOne =
      Metric.metricWeightAtLeastOne (metric dataSet)
  ; Bridge.SharedMarkedWeightedInfluenceBridge.weightTriangle =
      Metric.metricWeightTriangle (metric dataSet)
  ; Bridge.SharedMarkedWeightedInfluenceBridge.weightedGeneratorRowBelowSharedHessian =
      weightedGeneratorRowBelowSharedHessian dataSet
  }

metricWeightedPowerRowBound :
  ∀ {Scale Volume Root Site}
    (dataSet : SharedMarkedMetricInfluenceBridge Scale Volume Root Site)
    n x →
  Weighted.weightedPowerRow
    (Bridge.asWeightedFiniteInfluence (asWeightedBridge dataSet)) n x
  ≤ Power.rationalPower
      (Shared.hessianAnalyticConstant (shared dataSet)) (suc n)
metricWeightedPowerRowBound dataSet =
  Bridge.weightedGeneratorPowerRowBound (asWeightedBridge dataSet)

sharedMarkedMetricToWeightedInfluenceLevel : ProofLevel
sharedMarkedMetricToWeightedInfluenceLevel = machineChecked

sharedMarkedMetricToAllWeightedPowerRowsLevel : ProofLevel
sharedMarkedMetricToAllWeightedPowerRowsLevel = machineChecked

-- This is now the preferred C-spatial physical leaf: identify the SAME
-- Heat/Doob derivative generator and CMP116 Hessian mark on the literal lattice
-- metric, then prove the single weighted row inequality above.
literalSameDensityMetricGeneratorRowLevel : ProofLevel
literalSameDensityMetricGeneratorRowLevel = conditional
