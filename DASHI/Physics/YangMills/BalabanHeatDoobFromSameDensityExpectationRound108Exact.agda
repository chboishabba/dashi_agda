{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanHeatDoobFromSameDensityExpectationRound108Exact where

------------------------------------------------------------------------
-- ROUND108 BC2: ONE SAME-DENSITY EXPECTATION, COVARIANCE BY DEFINITION
--
-- The Round103 calculus carried both an expectation and a covariance together
-- with a covariance-definition equality.  Backward from the actual consumer,
-- covariance has no independent physical freedom:
--
--   Cov_t(f,g) = E_t(fg) - E_t(f) E_t(g).
--
-- Therefore a literal compact-group Heat/Doob instantiation only needs the
-- tilted expectation on the Round103 carrier, the first variation, and the
-- standard log-heat Hessian identity written using the covariance below.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _-ℝ_; _*ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanHeatDoobSameDensityLogHessianRound103Exact as Heat

record SameDensityHeatExpectation
    (carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier) : Set₁ where
  field
    Time : Set

    firstVariation :
      (Source.Background (Carrier.source carrier) → ℝ) →
      Source.Background (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier) → ℝ

    expectation :
      Time → Source.Background (Carrier.source carrier) →
      (Source.Background (Carrier.source carrier) → ℝ) → ℝ

    heatDoobHessian :
      Time → Source.Background (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier) → ℝ

    -- Standard differentiation identity, now stated against the covariance
    -- generated from this exact expectation rather than an independent object.
    logHeatHessianIdentity : ∀ time background u v →
      heatDoobHessian time background u v
      ≡ expectation time background
          (λ y → Carrier.cmp116PhysicalMarkedHessian carrier y u v)
        -ℝ
          ( expectation time background
              (λ y →
                firstVariation (Carrier.effectivePotential carrier) y u
                *ℝ firstVariation (Carrier.effectivePotential carrier) y v)
            -ℝ
              ( expectation time background
                  (λ y → firstVariation (Carrier.effectivePotential carrier) y u)
                *ℝ expectation time background
                  (λ y → firstVariation (Carrier.effectivePotential carrier) y v) ) )

open SameDensityHeatExpectation public

derivedCovariance :
  ∀ {carrier}
    (dataSet : SameDensityHeatExpectation carrier) →
  Time dataSet → Source.Background (Carrier.source carrier) →
  (Source.Background (Carrier.source carrier) → ℝ) →
  (Source.Background (Carrier.source carrier) → ℝ) → ℝ
derivedCovariance dataSet time background f g =
  expectation dataSet time background (λ y → f y *ℝ g y)
    -ℝ (expectation dataSet time background f
      *ℝ expectation dataSet time background g)

asRound103HeatDoobCalculus :
  ∀ {carrier} →
  SameDensityHeatExpectation carrier →
  Heat.HeatDoobSameDensityCalculus carrier
asRound103HeatDoobCalculus dataSet = record
  { Heat.HeatDoobSameDensityCalculus.Time = Time dataSet
  ; Heat.HeatDoobSameDensityCalculus.firstVariation = firstVariation dataSet
  ; Heat.HeatDoobSameDensityCalculus.heatTiltExpectation = expectation dataSet
  ; Heat.HeatDoobSameDensityCalculus.heatTiltCovariance = derivedCovariance dataSet
  ; Heat.HeatDoobSameDensityCalculus.covarianceDefinition =
      λ time background f g → refl
  ; Heat.HeatDoobSameDensityCalculus.heatDoobHessian = heatDoobHessian dataSet
  ; Heat.HeatDoobSameDensityCalculus.logHeatHessianIdentity =
      logHeatHessianIdentity dataSet
  }

round108SameDensityExpectationToHeatDoobLevel : ProofLevel
round108SameDensityExpectationToHeatDoobLevel = machineChecked

-- Physical BC2 leaf: instantiate the normalized compact-group heat-kernel tilted
-- expectation and first variation on the exact BC1 carrier.  Covariance is no
-- longer an independent source theorem.  The log-Hessian identity itself is
-- standard compact-manifold differentiation once that expectation is literal.
literalCompactGroupHeatTiltExpectationRound108Level : ProofLevel
literalCompactGroupHeatTiltExpectationRound108Level = conditional
