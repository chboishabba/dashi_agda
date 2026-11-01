{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanHeatDoobSameDensityLogHessianRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC2: SAME-DENSITY HEAT/DOOB LOG-HESSIAN IDENTITY
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _-ℝ_; _*ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source

record HeatDoobSameDensityCalculus
    (carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier) : Set₁ where
  field
    Time : Set

    firstVariation :
      (Source.Background (Carrier.source carrier) → ℝ) →
      Source.Background (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier) → ℝ

    heatTiltExpectation :
      Time → Source.Background (Carrier.source carrier) →
      (Source.Background (Carrier.source carrier) → ℝ) → ℝ

    heatTiltCovariance :
      Time → Source.Background (Carrier.source carrier) →
      (Source.Background (Carrier.source carrier) → ℝ) →
      (Source.Background (Carrier.source carrier) → ℝ) → ℝ

    covarianceDefinition : ∀ time background f g →
      heatTiltCovariance time background f g
      ≡ heatTiltExpectation time background (λ y → f y *ℝ g y)
          -ℝ (heatTiltExpectation time background f
              *ℝ heatTiltExpectation time background g)

    heatDoobHessian :
      Time → Source.Background (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier) → ℝ

    logHeatHessianIdentity : ∀ time background u v →
      heatDoobHessian time background u v
      ≡ heatTiltExpectation time background
          (λ y → Carrier.cmp116PhysicalMarkedHessian carrier y u v)
        -ℝ heatTiltCovariance time background
          (λ y → firstVariation (Carrier.effectivePotential carrier) y u)
          (λ y → firstVariation (Carrier.effectivePotential carrier) y v)

open HeatDoobSameDensityCalculus public

carrierGradient :
  ∀ {carrier}
    (dataSet : HeatDoobSameDensityCalculus carrier) →
  Source.Background (Carrier.source carrier) →
  Source.Tangent (Carrier.source carrier) → ℝ
carrierGradient {carrier} dataSet =
  firstVariation dataSet (Carrier.effectivePotential carrier)

conditionalExpectedStaticHessian :
  ∀ {carrier}
    (dataSet : HeatDoobSameDensityCalculus carrier) →
  Time dataSet → Source.Background (Carrier.source carrier) →
  Source.Tangent (Carrier.source carrier) →
  Source.Tangent (Carrier.source carrier) → ℝ
conditionalExpectedStaticHessian {carrier} dataSet time background u v =
  heatTiltExpectation dataSet time background
    (λ y → Carrier.cmp116PhysicalMarkedHessian carrier y u v)

conditionalGradientCovariance :
  ∀ {carrier}
    (dataSet : HeatDoobSameDensityCalculus carrier) →
  Time dataSet → Source.Background (Carrier.source carrier) →
  Source.Tangent (Carrier.source carrier) →
  Source.Tangent (Carrier.source carrier) → ℝ
conditionalGradientCovariance dataSet time background u v =
  heatTiltCovariance dataSet time background
    (λ y → carrierGradient dataSet y u)
    (λ y → carrierGradient dataSet y v)

heatDoobHessianIsStaticMinusCovariance :
  ∀ {carrier}
    (dataSet : HeatDoobSameDensityCalculus carrier) →
  ∀ time background u v →
  heatDoobHessian dataSet time background u v
  ≡ conditionalExpectedStaticHessian dataSet time background u v
      -ℝ conditionalGradientCovariance dataSet time background u v
heatDoobHessianIsStaticMinusCovariance dataSet =
  logHeatHessianIdentity dataSet

sameDensityHeatDoobIdentityWiringLevel : ProofLevel
sameDensityHeatDoobIdentityWiringLevel = machineChecked

heatDoobLogHessianConditionalCovarianceIdentityLevel : ProofLevel
heatDoobLogHessianConditionalCovarianceIdentityLevel = standardImported

literalYMSameDensityHeatDoobIdentificationLevel : ProofLevel
literalYMSameDensityHeatDoobIdentificationLevel = conditional
