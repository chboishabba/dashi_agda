{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1PathDefinedBC2Exact where

------------------------------------------------------------------------
-- R1 MAX-CUT: DEFINE BC2 FIRST VARIATION BY THE LITERAL SOURCE PATH.
--
-- The generic BC2 source record accepts an arbitrary `firstVariation`, then
-- downstream P1 must prove that it is the derivative along the selected compact
-- gauge path.  That is avoidable presentation freedom.
--
-- Preferred source presentation: choose the path and derivative calculus first,
-- define
--
--   firstVariation f B X = d/dt f(path B X t)|_{t=0},
--
-- and state the standard compact-group heat/log-Hessian theorem directly with
-- this derivative.  Compilation to the existing BC2 API is then definitional.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _-ℝ_; _*ℝ_)

import DASHI.Physics.Foundations.CMP119CosmologyP1InvariantPathDerivativeCovarianceExact as Path
import DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact as BC2
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source

pathFirstVariation :
  ∀ {carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier} →
  Path.SignedPathDerivativeLaws →
  (Source.Background (Carrier.source carrier) →
   Source.Tangent (Carrier.source carrier) → ℝ →
   Source.Background (Carrier.source carrier)) →
  (Source.Background (Carrier.source carrier) → ℝ) →
  Source.Background (Carrier.source carrier) →
  Source.Tangent (Carrier.source carrier) → ℝ
pathFirstVariation derivativeLaws sourcePath f background tangent =
  Path.derivativeAtZero derivativeLaws
    (λ t → f (sourcePath background tangent t))

record PathDefinedCompactGroupHeatDoobOnCarrier
    (carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier)
    (derivativeLaws : Path.SignedPathDerivativeLaws)
    (sourcePath :
      Source.Background (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier) → ℝ →
      Source.Background (Carrier.source carrier))
    : Set₁ where
  field
    Time : Set

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

    compactGroupLogHeatHessianIdentity : ∀ time background u v →
      heatDoobHessian time background u v
      ≡ heatTiltExpectation time background
          (λ y → Carrier.cmp116PhysicalMarkedHessian carrier y u v)
        -ℝ heatTiltCovariance time background
          (λ y → pathFirstVariation derivativeLaws sourcePath
            (Carrier.effectivePotential carrier) y u)
          (λ y → pathFirstVariation derivativeLaws sourcePath
            (Carrier.effectivePotential carrier) y v)

open PathDefinedCompactGroupHeatDoobOnCarrier public

asCompactGroupHeatDoobOnCarrier :
  ∀ {carrier derivativeLaws sourcePath} →
  PathDefinedCompactGroupHeatDoobOnCarrier
    carrier derivativeLaws sourcePath →
  BC2.CompactGroupHeatDoobOnCarrier carrier
asCompactGroupHeatDoobOnCarrier
    {derivativeLaws = derivativeLaws} {sourcePath = sourcePath} data = record
  { BC2.CompactGroupHeatDoobOnCarrier.Time = Time data
  ; BC2.CompactGroupHeatDoobOnCarrier.firstVariation =
      pathFirstVariation derivativeLaws sourcePath
  ; BC2.CompactGroupHeatDoobOnCarrier.heatTiltExpectation =
      heatTiltExpectation data
  ; BC2.CompactGroupHeatDoobOnCarrier.heatTiltCovariance =
      heatTiltCovariance data
  ; BC2.CompactGroupHeatDoobOnCarrier.covarianceDefinition =
      covarianceDefinition data
  ; BC2.CompactGroupHeatDoobOnCarrier.heatDoobHessian =
      heatDoobHessian data
  ; BC2.CompactGroupHeatDoobOnCarrier.compactGroupLogHeatHessianIdentity =
      compactGroupLogHeatHessianIdentity data
  }

compiledBC2FirstVariationIsPathDerivative :
  ∀ {carrier derivativeLaws sourcePath}
    (data :
      PathDefinedCompactGroupHeatDoobOnCarrier
        carrier derivativeLaws sourcePath) →
  ∀ f background tangent →
  BC2.firstVariation (asCompactGroupHeatDoobOnCarrier data)
    f background tangent
  ≡ pathFirstVariation derivativeLaws sourcePath f background tangent
compiledBC2FirstVariationIsPathDerivative data f background tangent = refl

bc2FirstVariationIsPathDerivativeByDefinition : Bool
bc2FirstVariationIsPathDerivativeByDefinition = true

pathDefinedBC2KeepsExactCarrierPotential : Bool
pathDefinedBC2KeepsExactCarrierPotential = true

remainingBC2SourceTheoremIsStandardCompactGroupLogHeatIdentity : Bool
remainingBC2SourceTheoremIsStandardCompactGroupLogHeatIdentity = true
