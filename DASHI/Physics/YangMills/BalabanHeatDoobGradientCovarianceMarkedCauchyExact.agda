{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanHeatDoobGradientCovarianceMarkedCauchyExact where

------------------------------------------------------------------------
-- ROUND102 B->C: COVARIANCE NEEDS FIRST-DERIVATIVE LOCALITY, NOT A NEW HESSIAN
--
-- For a log/Doob transform the extra Hessian term is a covariance of first
-- derivatives.  After absolute majorisation, the standard probability estimate
-- has the schematic form
--
--       |Cov(F,G)| <= 2 ||F||_infty ||G||_infty.
--
-- Therefore if one derivative response carries the CMP116 marked spatial/RG
-- shell while the companion derivative is uniformly bounded on the SAME
-- analytic polydisc, the covariance inherits the SAME shell.  This file proves
-- the exact shell and weighted-row arithmetic after that standard covariance
-- inequality has been instantiated.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact as Weighted
import DASHI.Physics.YangMills.BalabanThreeHalvesMetricWeightExact as Metric

two : ℚ
two = + 2 / 1

twoNonnegative : 0ℚ ≤ two
twoNonnegative = ℚP.nonNegative⁻¹ two

mulNN : ∀ {a b : ℚ} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a * b
mulNN {a} {b} aNN bNN =
  let
    instance
      aNonnegative : NonNegative a
      aNonnegative = ℚ.nonNegative aNN
      bNonnegative : NonNegative b
      bNonnegative = ℚ.nonNegative bNN
  in
  ℚP.nonNegative⁻¹ (a * b)

------------------------------------------------------------------------
-- TEMPORAL / RG-SHELL COVARIANCE
------------------------------------------------------------------------

record HeatDoobTemporalGradientCovariance : Set₁ where
  field
    localizedGradientShell : Nat → ℚ
    localizedGradientNonnegative : ∀ n → 0ℚ ≤ localizedGradientShell n

    gradientAmplitude : ℚ
    gradientAmplitudeNonnegative : 0ℚ ≤ gradientAmplitude
    localizedGradientGeometricHalf : ∀ n →
      localizedGradientShell n ≤ gradientAmplitude * Geo.halfPower n

    companionGradientBound : ℚ
    companionGradientBoundNonnegative : 0ℚ ≤ companionGradientBound

    covarianceDebt : Nat → ℚ
    covarianceDebtNonnegative : ∀ n → 0ℚ ≤ covarianceDebt n

    covarianceBelowTwoGradientProducts : ∀ n →
      covarianceDebt n
      ≤ two * (localizedGradientShell n * companionGradientBound)

open HeatDoobTemporalGradientCovariance public

temporalCovarianceAmplitude : HeatDoobTemporalGradientCovariance → ℚ
temporalCovarianceAmplitude dataSet =
  two * (gradientAmplitude dataSet * companionGradientBound dataSet)

temporalCovarianceAmplitudeNonnegative :
  (dataSet : HeatDoobTemporalGradientCovariance) →
  0ℚ ≤ temporalCovarianceAmplitude dataSet
temporalCovarianceAmplitudeNonnegative dataSet =
  mulNN twoNonnegative
    (mulNN
      (gradientAmplitudeNonnegative dataSet)
      (companionGradientBoundNonnegative dataSet))

temporalCovarianceGeometricHalf :
  (dataSet : HeatDoobTemporalGradientCovariance) n →
  covarianceDebt dataSet n
  ≤ temporalCovarianceAmplitude dataSet * Geo.halfPower n
temporalCovarianceGeometricHalf dataSet n =
  let
    companionNN = companionGradientBoundNonnegative dataSet
    first = covarianceBelowTwoGradientProducts dataSet n
    localized = localizedGradientGeometricHalf dataSet n
    scaledCompanion = Norm.scaleRight companionNN localized
    scaledTwo = Norm.scaleNonnegative two twoNonnegative scaledCompanion
  in
  ℚP.≤-trans first
    (subst
      (λ right →
        two * (localizedGradientShell dataSet n * companionGradientBound dataSet)
        ≤ right)
      (ℚRing.solve-∀
        two
        (gradientAmplitude dataSet)
        (companionGradientBound dataSet)
        (Geo.halfPower n))
      scaledTwo)

------------------------------------------------------------------------
-- SPATIAL WEIGHTED-ROW COVARIANCE
------------------------------------------------------------------------

record HeatDoobSpatialGradientCovariance (Site : Set) : Set₁ where
  field
    sites : List Site
    metric : Metric.NatMetricTriangle Site

    localizedGradient covarianceInfluence : Site → Site → ℚ
    localizedGradientNonnegative : ∀ x y → 0ℚ ≤ localizedGradient x y
    covarianceInfluenceNonnegative : ∀ x y → 0ℚ ≤ covarianceInfluence x y

    companionGradientBound : ℚ
    companionGradientBoundNonnegative : 0ℚ ≤ companionGradientBound

    gradientWeightedRowMass : ℚ
    gradientWeightedRowMassNonnegative : 0ℚ ≤ gradientWeightedRowMass
    gradientWeightedRowBound : ∀ x →
      Sums.sumRational sites
        (λ y → Metric.metricWeight metric x y * localizedGradient x y)
      ≤ gradientWeightedRowMass

    covarianceBelowTwoGradientProducts : ∀ x y →
      covarianceInfluence x y
      ≤ two * (localizedGradient x y * companionGradientBound)

open HeatDoobSpatialGradientCovariance public

weightedCovariancePointwise :
  ∀ {Site} (dataSet : HeatDoobSpatialGradientCovariance Site) x y →
  Metric.metricWeight (metric dataSet) x y * covarianceInfluence dataSet x y
  ≤ two * companionGradientBound dataSet
      * (Metric.metricWeight (metric dataSet) x y * localizedGradient dataSet x y)
weightedCovariancePointwise dataSet x y =
  let
    weight = Metric.metricWeight (metric dataSet) x y
    weightNN = Metric.metricWeightNonnegative (metric dataSet) x y
    first = Norm.scaleNonnegative weight weightNN
      (covarianceBelowTwoGradientProducts dataSet x y)
  in
  subst
    (λ right →
      weight * covarianceInfluence dataSet x y ≤ right)
    (ℚRing.solve-∀
      weight two (localizedGradient dataSet x y) (companionGradientBound dataSet))
    first

spatialCovarianceRowMass :
  ∀ {Site} → HeatDoobSpatialGradientCovariance Site → ℚ
spatialCovarianceRowMass dataSet =
  two * companionGradientBound dataSet * gradientWeightedRowMass dataSet

spatialCovarianceRowMassNonnegative :
  ∀ {Site} (dataSet : HeatDoobSpatialGradientCovariance Site) →
  0ℚ ≤ spatialCovarianceRowMass dataSet
spatialCovarianceRowMassNonnegative dataSet =
  mulNN
    (mulNN twoNonnegative (companionGradientBoundNonnegative dataSet))
    (gradientWeightedRowMassNonnegative dataSet)

covarianceWeightedRowBound :
  ∀ {Site} (dataSet : HeatDoobSpatialGradientCovariance Site) x →
  Sums.sumRational (sites dataSet)
    (λ y → Metric.metricWeight (metric dataSet) x y * covarianceInfluence dataSet x y)
  ≤ spatialCovarianceRowMass dataSet
covarianceWeightedRowBound dataSet x =
  let
    pointwise = Weighted.sumMono
      (sites dataSet)
      (λ y → Metric.metricWeight (metric dataSet) x y * covarianceInfluence dataSet x y)
      (λ y →
        (two * companionGradientBound dataSet)
          * (Metric.metricWeight (metric dataSet) x y * localizedGradient dataSet x y))
      (weightedCovariancePointwise dataSet x)

    scaleNN = mulNN twoNonnegative (companionGradientBoundNonnegative dataSet)
    factored = Sums.sumRationalScale
      (two * companionGradientBound dataSet)
      (sites dataSet)
      (λ y → Metric.metricWeight (metric dataSet) x y * localizedGradient dataSet x y)

    scaled = Norm.scaleNonnegative
      (two * companionGradientBound dataSet)
      scaleNN
      (gradientWeightedRowBound dataSet x)
  in
  ℚP.≤-trans pointwise
    (subst
      (λ left → left ≤ spatialCovarianceRowMass dataSet)
      (sym factored)
      scaled)

------------------------------------------------------------------------
-- Authority boundary
------------------------------------------------------------------------

temporalGradientCovarianceShellCompilerLevel : ProofLevel
temporalGradientCovarianceShellCompilerLevel = machineChecked

spatialGradientCovarianceWeightedRowCompilerLevel : ProofLevel
spatialGradientCovarianceWeightedRowCompilerLevel = machineChecked

heatDoobBoundedGradientCovarianceInequalityLevel : ProofLevel
heatDoobBoundedGradientCovarianceInequalityLevel = standardImported

-- TRUE physical source seam after this reduction: instantiate one first-gradient
-- localized response and one uniform companion-gradient bound from the SAME
-- CMP116 common analytic polydisc / Heat-Doob density.  CMP116 Sect.1 explicitly
-- preserves localization under finite Cauchy differentiation; the remaining job
-- is literal coordinate/radius identification, not a new covariance cluster
-- expansion.
literalCMP116FirstGradientHeatDoobCovarianceInstantiationLevel : ProofLevel
literalCMP116FirstGradientHeatDoobCovarianceInstantiationLevel = conditional
