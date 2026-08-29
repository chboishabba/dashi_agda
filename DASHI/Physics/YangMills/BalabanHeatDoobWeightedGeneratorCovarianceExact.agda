{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanHeatDoobWeightedGeneratorCovarianceExact where

------------------------------------------------------------------------
-- ROUND101 SPATIAL CORRECTION: DYNAMIC GENERATOR = STATIC RESPONSE + COVARIANCE
--
-- As on the temporal Heat/Doob lane, identifying the dynamic derivative
-- generator directly with the static CMP116 Hessian is generally too strong.
-- The log/Doob transform carries an additional covariance response.
--
-- The shortest honest spatial bridge is therefore:
--
--   M_dynamic(x,y) <= M_static(x,y) + M_cov(x,y),
--
-- with the static weighted row identified with the already-controlled CMP116
-- Hessian partial row and only the covariance weighted row estimated anew.
-- Then
--
--   sum_y w M_dynamic <= C_H + C_cov,
--
-- and the existing weighted finite-influence theorem propagates that single row
-- through every Dyson power.  This keeps the exponential metric weight and
-- isolates the genuinely stochastic debt instead of hiding it in a false
-- same-object identity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact as Weighted
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanThreeHalvesMetricWeightExact as Metric
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanRootedKPToExponentialWeightedHessianExact as Hess

record HeatDoobWeightedGeneratorCovarianceSplit
    (Scale Volume Root Site : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    sites : List Site
    metric : Metric.NatMetricTriangle Site

    dynamicInfluence staticInfluence covarianceInfluence : Site → Site → ℚ
    dynamicNonnegative : ∀ x y → 0ℚ ≤ dynamicInfluence x y
    staticNonnegative : ∀ x y → 0ℚ ≤ staticInfluence x y
    covarianceNonnegative : ∀ x y → 0ℚ ≤ covarianceInfluence x y

    generatorSplit : ∀ x y →
      dynamicInfluence x y ≤ staticInfluence x y + covarianceInfluence x y

    rowDepth : Site → Nat

    -- Static derivative response is the CMP116 hessian row already controlled.
    staticRowIsMarkedHessianPartial : ∀ x →
      Sums.sumRational sites
        (λ y → Metric.metricWeight metric x y * staticInfluence x y)
      ≡ Hess.weightedHessianPartial
          (Shared.hessianWeightedControl shared)
          scale volume root (rowDepth x)

    covarianceRowMass : ℚ
    covarianceRowMassNonnegative : 0ℚ ≤ covarianceRowMass
    covarianceWeightedRowBound : ∀ x →
      Sums.sumRational sites
        (λ y → Metric.metricWeight metric x y * covarianceInfluence x y)
      ≤ covarianceRowMass

open HeatDoobWeightedGeneratorCovarianceSplit public

staticWeightedRowBound :
  ∀ {Scale Volume Root Site}
    (dataSet : HeatDoobWeightedGeneratorCovarianceSplit Scale Volume Root Site)
    x →
  Sums.sumRational (sites dataSet)
    (λ y → Metric.metricWeight (metric dataSet) x y * staticInfluence dataSet x y)
  ≤ Shared.hessianAnalyticConstant (shared dataSet)
staticWeightedRowBound dataSet x =
  subst
    (λ left → left ≤ Shared.hessianAnalyticConstant (shared dataSet))
    (staticRowIsMarkedHessianPartial dataSet x)
    (Shared.hessianWeightedInfluenceBelowAnalyticConstant
      (shared dataSet)
      (scale dataSet) (volume dataSet) (root dataSet) (rowDepth dataSet x))

weightedSplitPointwise :
  ∀ {Scale Volume Root Site}
    (dataSet : HeatDoobWeightedGeneratorCovarianceSplit Scale Volume Root Site)
    x y →
  Metric.metricWeight (metric dataSet) x y * dynamicInfluence dataSet x y
  ≤ Metric.metricWeight (metric dataSet) x y
      * (staticInfluence dataSet x y + covarianceInfluence dataSet x y)
weightedSplitPointwise dataSet x y =
  DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact.scaleNonnegative
    (Metric.metricWeight (metric dataSet) x y)
    (Metric.metricWeightNonnegative (metric dataSet) x y)
    (generatorSplit dataSet x y)

weightedDynamicRowBound :
  ∀ {Scale Volume Root Site}
    (dataSet : HeatDoobWeightedGeneratorCovarianceSplit Scale Volume Root Site)
    x →
  Sums.sumRational (sites dataSet)
    (λ y → Metric.metricWeight (metric dataSet) x y * dynamicInfluence dataSet x y)
  ≤ Shared.hessianAnalyticConstant (shared dataSet) + covarianceRowMass dataSet
weightedDynamicRowBound dataSet x =
  let
    pointwise = Weighted.sumMono
      (sites dataSet)
      (λ y → Metric.metricWeight (metric dataSet) x y * dynamicInfluence dataSet x y)
      (λ y → Metric.metricWeight (metric dataSet) x y
        * (staticInfluence dataSet x y + covarianceInfluence dataSet x y))
      (weightedSplitPointwise dataSet x)

    distribute :
      Sums.sumRational (sites dataSet)
        (λ y → Metric.metricWeight (metric dataSet) x y
          * (staticInfluence dataSet x y + covarianceInfluence dataSet x y))
      ≡
      Sums.sumRational (sites dataSet)
        (λ y → Metric.metricWeight (metric dataSet) x y * staticInfluence dataSet x y)
      +
      Sums.sumRational (sites dataSet)
        (λ y → Metric.metricWeight (metric dataSet) x y * covarianceInfluence dataSet x y)
    distribute = sumDistribute (sites dataSet)
      (λ y → Metric.metricWeight (metric dataSet) x y * staticInfluence dataSet x y)
      (λ y → Metric.metricWeight (metric dataSet) x y * covarianceInfluence dataSet x y)
      (λ y → Data.Rational.Tactic.RingSolver.solve-∀
        (Metric.metricWeight (metric dataSet) x y)
        (staticInfluence dataSet x y)
        (covarianceInfluence dataSet x y))

    components = ℚP.+-mono-≤
      (staticWeightedRowBound dataSet x)
      (covarianceWeightedRowBound dataSet x)
  in
  ℚP.≤-trans pointwise (subst
    (λ left → left ≤ Shared.hessianAnalyticConstant (shared dataSet) + covarianceRowMass dataSet)
    distribute components)
  where
    sumDistribute :
      ∀ {A : Set} (xs : List A) (f g : A → ℚ) →
      (∀ a →
        Metric.metricWeight (metric dataSet) x a
          * (staticInfluence dataSet x a + covarianceInfluence dataSet x a)
        ≡ f a + g a) →
      Sums.sumRational xs
        (λ a → Metric.metricWeight (metric dataSet) x a
          * (staticInfluence dataSet x a + covarianceInfluence dataSet x a))
      ≡ Sums.sumRational xs f + Sums.sumRational xs g
    sumDistribute [] f g pointwise = refl
    sumDistribute (a Agda.Builtin.List.∷ as) f g pointwise
      rewrite pointwise a | sumDistribute as f g pointwise =
      Data.Rational.Tactic.RingSolver.solve-∀
        (f a) (g a) (Sums.sumRational as f) (Sums.sumRational as g)

asWeightedDynamicMajorant :
  ∀ {Scale Volume Root Site} →
  HeatDoobWeightedGeneratorCovarianceSplit Scale Volume Root Site →
  Weighted.WeightedFiniteInfluenceMajorant Site
asWeightedDynamicMajorant dataSet = record
  { Weighted.WeightedFiniteInfluenceMajorant.sites = sites dataSet
  ; Weighted.WeightedFiniteInfluenceMajorant.influence = dynamicInfluence dataSet
  ; Weighted.WeightedFiniteInfluenceMajorant.weight = Metric.metricWeight (metric dataSet)
  ; Weighted.WeightedFiniteInfluenceMajorant.influenceNonnegative = dynamicNonnegative dataSet
  ; Weighted.WeightedFiniteInfluenceMajorant.weightNonnegative =
      Metric.metricWeightNonnegative (metric dataSet)
  ; Weighted.WeightedFiniteInfluenceMajorant.weightAtLeastOne =
      Metric.metricWeightAtLeastOne (metric dataSet)
  ; Weighted.WeightedFiniteInfluenceMajorant.weightTriangle =
      Metric.metricWeightTriangle (metric dataSet)
  ; Weighted.WeightedFiniteInfluenceMajorant.weightedRowMass =
      Shared.hessianAnalyticConstant (shared dataSet) + covarianceRowMass dataSet
  ; Weighted.WeightedFiniteInfluenceMajorant.weightedRowMassNonnegative =
      ℚP.+-mono-≤
        (Shared.markedConstantNonnegative (shared dataSet) Shared.hessianMark)
        (covarianceRowMassNonnegative dataSet)
  ; Weighted.WeightedFiniteInfluenceMajorant.weightedRowMassBound =
      weightedDynamicRowBound dataSet
  }

allDynamicWeightedPowerRows :
  ∀ {Scale Volume Root Site}
    (dataSet : HeatDoobWeightedGeneratorCovarianceSplit Scale Volume Root Site)
    n x →
  Weighted.weightedPowerRow (asWeightedDynamicMajorant dataSet) n x
  ≤ Power.rationalPower
      (Shared.hessianAnalyticConstant (shared dataSet) + covarianceRowMass dataSet)
      (Agda.Builtin.Nat.suc n)
allDynamicWeightedPowerRows dataSet = Weighted.weightedPowerRowBound
  (asWeightedDynamicMajorant dataSet)

heatDoobWeightedGeneratorCovarianceCompilerLevel : ProofLevel
heatDoobWeightedGeneratorCovarianceCompilerLevel = machineChecked

heatDoobWeightedGeneratorAllPowerRowsLevel : ProofLevel
heatDoobWeightedGeneratorAllPowerRowsLevel = machineChecked

-- Remaining spatial physical leaf is now the covariance response estimate plus
-- source identification of the static response with CMP116.  A direct dynamic=
-- static Hessian identity is not assumed.
literalHeatDoobWeightedCovarianceInstantiationLevel : ProofLevel
literalHeatDoobWeightedCovarianceInstantiationLevel = conditional
