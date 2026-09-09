{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanHeatDoobExpectationContractionRound254Exact where

------------------------------------------------------------------------
-- ROUND254 / NORMALIZED HEAT EXPECTATION PRESERVES POINTWISE MAJORANTS
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2RationalShellBudgetToRealRound108Exact as Embed
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanHeatDoobFromSameDensityExpectationRound108Exact as Heat
import DASHI.Physics.YangMills.BalabanHeatDoobSameDensityLogHessianRound103Exact as LogHeat

record NormalizedHeatTiltExpectationContraction
    {carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier}
    (heat : Heat.SameDensityHeatExpectation carrier) : Set₁ where
  field
    expectationAbsoluteContraction :
      ∀ time background
        (f : Source.Background (Carrier.source carrier) → ℝ)
        bound →
      (∀ y → absℝ (f y) ≤ℝ bound) →
      absℝ (Heat.expectation heat time background f) ≤ℝ bound

open NormalizedHeatTiltExpectationContraction public

record PointwiseStaticHessianMajorant
    {carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier}
    (heat : Heat.SameDensityHeatExpectation carrier)
    (contraction : NormalizedHeatTiltExpectationContraction heat)
    (embedding : Embed.OrderedRationalRealRingEmbedding) : Set₁ where
  field
    time : Heat.Time heat
    background : Source.Background (Carrier.source carrier)
    u v : Source.Tangent (Carrier.source carrier)

    rationalBound : ℚ

    pointwiseStaticHessianBound : ∀ y →
      absℝ (Carrier.cmp116PhysicalMarkedHessian carrier y u v)
      ≤ℝ Embed.embed embedding rationalBound

open PointwiseStaticHessianMajorant public

conditionalStaticHessianMajorized :
  ∀ {carrier heat contraction embedding}
    (dataSet : PointwiseStaticHessianMajorant
      {carrier = carrier} heat contraction embedding) →
  absℝ
    (LogHeat.conditionalExpectedStaticHessian
      (Heat.asRound103HeatDoobCalculus heat)
      (time dataSet) (background dataSet) (u dataSet) (v dataSet))
  ≤ℝ Embed.embed embedding (rationalBound dataSet)
conditionalStaticHessianMajorized {heat = heat} {contraction = contraction} dataSet =
  expectationAbsoluteContraction contraction
    (time dataSet) (background dataSet)
    (λ y → Carrier.cmp116PhysicalMarkedHessian _ y (u dataSet) (v dataSet))
    (Embed.embed _ (rationalBound dataSet))
    (pointwiseStaticHessianBound dataSet)

normalizedHeatExpectationContractionLevel : ProofLevel
normalizedHeatExpectationContractionLevel = standardImported

staticHessianExpectationMajorantCompilerLevel : ProofLevel
staticHessianExpectationMajorantCompilerLevel = machineChecked

-- No independent YM leaf is introduced here.  The literal compact-group heat
-- expectation is already the BC2 physical instantiation, and the pointwise
-- CMP116 Hessian/source majorant remains a source-coordinate identification.
