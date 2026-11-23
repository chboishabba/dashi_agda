{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact where

------------------------------------------------------------------------
-- ROUND119 BC2 BIDI: THE COMPACT-GROUP HEAT FLOW USES THE BC1 POTENTIAL BY TYPE
--
-- Backward consumer: Round103 needs a `HeatDoobSameDensityCalculus carrier`.
-- Forward source: on the finite compact Lie carrier G^E, the standard normalized
-- Haar/Laplace--Beltrami heat semigroup is applied to
--
--       exp(- V),
--
-- where V is the finite-cutoff effective potential.  Do not carry a second
-- anonymous initial density and later assert it is the CMP109/CMP116 density.
-- This source record mentions `Carrier.effectivePotential carrier` literally in
-- every first-gradient/log-Hessian identity, so SAME DENSITY is structural.
--
-- The standard calculus identity is
--
--   Hess V_t = E_t[Hess V] - Cov_t(grad V,grad V).
--
-- Its Riemannian compact-group proof is imported analysis.  The DASHI compiler
-- below is exact plumbing from that source theorem to Round103's consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _-ℝ_; _*ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanHeatDoobSameDensityLogHessianRound103Exact as Heat

record CompactGroupHeatDoobOnCarrier
    (carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier) : Set₁ where
  field
    Time : Set

    firstVariation :
      (Source.Background (Carrier.source carrier) → ℝ) →
      Source.Background (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier) → ℝ

    -- These are the normalized compact-group heat-tilted expectation and
    -- covariance generated from exp(- Carrier.effectivePotential carrier).
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

    -- Standard compact-Riemannian log-heat identity, stated on the EXACT BC1
    -- potential and exact CMP116 physical composite Hessian.
    compactGroupLogHeatHessianIdentity : ∀ time background u v →
      heatDoobHessian time background u v
      ≡ heatTiltExpectation time background
          (λ y → Carrier.cmp116PhysicalMarkedHessian carrier y u v)
        -ℝ heatTiltCovariance time background
          (λ y → firstVariation (Carrier.effectivePotential carrier) y u)
          (λ y → firstVariation (Carrier.effectivePotential carrier) y v)

open CompactGroupHeatDoobOnCarrier public

asRound103SameDensityCalculus :
  ∀ {carrier} →
  CompactGroupHeatDoobOnCarrier carrier →
  Heat.HeatDoobSameDensityCalculus carrier
asRound103SameDensityCalculus dataSet = record
  { Heat.HeatDoobSameDensityCalculus.Time = Time dataSet
  ; Heat.HeatDoobSameDensityCalculus.firstVariation = firstVariation dataSet
  ; Heat.HeatDoobSameDensityCalculus.heatTiltExpectation = heatTiltExpectation dataSet
  ; Heat.HeatDoobSameDensityCalculus.heatTiltCovariance = heatTiltCovariance dataSet
  ; Heat.HeatDoobSameDensityCalculus.covarianceDefinition = covarianceDefinition dataSet
  ; Heat.HeatDoobSameDensityCalculus.heatDoobHessian = heatDoobHessian dataSet
  ; Heat.HeatDoobSameDensityCalculus.logHeatHessianIdentity =
      compactGroupLogHeatHessianIdentity dataSet
  }

compactGroupHessianIsStaticMinusCovariance :
  ∀ {carrier}
    (dataSet : CompactGroupHeatDoobOnCarrier carrier) →
  ∀ time background u v →
  heatDoobHessian dataSet time background u v
  ≡ Heat.conditionalExpectedStaticHessian
      (asRound103SameDensityCalculus dataSet) time background u v
      -ℝ Heat.conditionalGradientCovariance
        (asRound103SameDensityCalculus dataSet) time background u v
compactGroupHessianIsStaticMinusCovariance dataSet =
  Heat.heatDoobHessianIsStaticMinusCovariance
    (asRound103SameDensityCalculus dataSet)

bc2CompactGroupToSameDensityCompilerLevel : ProofLevel
bc2CompactGroupToSameDensityCompilerLevel = machineChecked

bc2SamePotentialStaticMinusCovarianceLevel : ProofLevel
bc2SamePotentialStaticMinusCovarianceLevel = machineChecked

-- The compact Riemannian/Haar heat log-Hessian formula is standard analysis.
-- Importantly, its potential argument above is not an abstract V: it is the
-- exact Round103 carrier potential by type.
compactGroupLogHeatHessianSourceLevel : ProofLevel
compactGroupLogHeatHessianSourceLevel = standardImported

-- Remaining physical instantiation is only the concrete finite-product compact
-- Lie heat semigroup / Haar expectation on the repository's literal gauge
-- configuration carrier.  No separate "same density" equality remains.
literalFiniteGaugeGroupHeatSemigroupInstantiationLevel : ProofLevel
literalFiniteGaugeGroupHeatSemigroupInstantiationLevel = conditional
