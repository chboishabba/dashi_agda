{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSharedMarkedHessianGeneratorRowExact where

------------------------------------------------------------------------
-- ROW C SPATIAL: IF THE GENERATOR ROW IS THE CMP116 HESSIAN ROW, THE BOUND IS FREE
--
-- The previous weighted bridge still exposed the analytic inequality
--
--   sum_y (3/2)^d M(x,y) <= C_H
--
-- as a physical field.  But the shared marked CMP116 carrier already proves
-- exactly that its weighted Hessian partial row is <= C_H.  Therefore the
-- highest-alpha source task is not a second estimate: it is the SAME-OBJECT
-- identity/comparison saying that the absolute covariant derivative-generator
-- row used by Heat/Doob is the physical Hessian row already represented by the
-- hessian mark.
--
-- This adapter makes that distinction explicit.  If, for each finite row, the
-- weighted generator sum is identified with one sufficiently complete weighted
-- Hessian partial sum, the uniform row bound follows immediately from the
-- existing CMP116 compiler.  Then all weighted Dyson powers are downstream.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanRootedKPToExponentialWeightedHessianExact as Hess
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanThreeHalvesMetricWeightExact as Metric
import DASHI.Physics.YangMills.BalabanSharedMarkedMetricInfluenceExact as Influence
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianToWeightedInfluenceExact as WeightedBridge
import DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact as Weighted
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

record LiteralHessianGeneratorRowIdentification
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

    -- The finite shell depth that contains the literal row represented by x.
    rowDepth : Site → Nat

    -- This is the actual physical/source seam.  No new numerical estimate is
    -- hidden here: it identifies the weighted generator row with the weighted
    -- CMP116 hessian response already controlled on the same density/metric.
    generatorRowIsMarkedHessianPartial : ∀ x →
      Sums.sumRational sites
        (λ y → Metric.metricWeight metric x y * influence x y)
      ≡ Hess.weightedHessianPartial
          (Shared.hessianWeightedControl shared)
          scale volume root (rowDepth x)

open LiteralHessianGeneratorRowIdentification public

weightedGeneratorRowBound :
  ∀ {Scale Volume Root Site}
    (dataSet : LiteralHessianGeneratorRowIdentification Scale Volume Root Site)
    x →
  Sums.sumRational (sites dataSet)
    (λ y → Metric.metricWeight (metric dataSet) x y * influence dataSet x y)
  ≤ Shared.hessianAnalyticConstant (shared dataSet)
weightedGeneratorRowBound dataSet x =
  subst
    (λ left → left ≤ Shared.hessianAnalyticConstant (shared dataSet))
    (generatorRowIsMarkedHessianPartial dataSet x)
    (Shared.hessianWeightedInfluenceBelowAnalyticConstant
      (shared dataSet)
      (scale dataSet)
      (volume dataSet)
      (root dataSet)
      (rowDepth dataSet x))

asMetricInfluenceBridge :
  ∀ {Scale Volume Root Site} →
  LiteralHessianGeneratorRowIdentification Scale Volume Root Site →
  Influence.SharedMarkedMetricInfluenceBridge Scale Volume Root Site
asMetricInfluenceBridge dataSet = record
  { Influence.SharedMarkedMetricInfluenceBridge.shared = shared dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.scale = scale dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.volume = volume dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.root = root dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.sites = sites dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.metric = metric dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.influence = influence dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.influenceNonnegative =
      influenceNonnegative dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.weightedGeneratorRowBelowSharedHessian =
      weightedGeneratorRowBound dataSet
  }

allWeightedGeneratorPowersBound :
  ∀ {Scale Volume Root Site}
    (dataSet : LiteralHessianGeneratorRowIdentification Scale Volume Root Site)
    n x →
  Weighted.weightedPowerRow
    (WeightedBridge.asWeightedFiniteInfluence
      (Influence.asWeightedBridge (asMetricInfluenceBridge dataSet)))
    n x
  ≤ Power.rationalPower
      (Shared.hessianAnalyticConstant (shared dataSet))
      (Agda.Builtin.Nat.suc n)
allWeightedGeneratorPowersBound dataSet =
  Influence.metricWeightedPowerRowBound (asMetricInfluenceBridge dataSet)

sameObjectGeneratorRowToUniformWeightedBoundLevel : ProofLevel
sameObjectGeneratorRowToUniformWeightedBoundLevel = machineChecked

sameObjectGeneratorRowToAllDysonPowerRowsLevel : ProofLevel
sameObjectGeneratorRowToAllDysonPowerRowsLevel = machineChecked

-- Preferred physical Row-C spatial seam after this reduction: prove the literal
-- Heat/Doob derivative-generator weighted row is the SAME physical Hessian row
-- produced by CMP116 (with a finite shell depth containing the row).  The
-- quantitative C_H inequality is then not a second analytic theorem.
literalHeatDoobGeneratorIsCMP116HessianRowLevel : ProofLevel
literalHeatDoobGeneratorIsCMP116HessianRowLevel = conditional
