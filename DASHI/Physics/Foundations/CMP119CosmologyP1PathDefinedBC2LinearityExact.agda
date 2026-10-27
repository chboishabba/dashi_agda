{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1PathDefinedBC2LinearityExact where

------------------------------------------------------------------------
-- R1 ORDINARY ANALYSIS: PATH DERIVATIVE -> ROUND142/143 LINEARITY.
--
-- Once firstVariation is definitionally the derivative of f(path(t)), the
-- congruence/zero/additivity laws consumed by Round142/143 are ordinary
-- one-variable derivative algebra.  Keep them in one reusable authority and
-- compile the finite effective-action first-variation calculus directly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _+ℝ_)

import DASHI.Physics.Foundations.CMP119CosmologyP1InvariantPathDerivativeCovarianceExact as Path
import DASHI.Physics.Foundations.CMP119CosmologyP1PathDefinedBC2Exact as PathBC2
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source

record LinearSignedPathDerivativeLaws : Set₁ where
  field
    signedLaws : Path.SignedPathDerivativeLaws

    derivativeZero :
      Path.derivativeAtZero signedLaws (λ _ → 0ℝ) ≡ 0ℝ

    derivativeAdd :
      ∀ f g →
      Path.derivativeAtZero signedLaws (λ t → f t +ℝ g t)
      ≡
      Path.derivativeAtZero signedLaws f
      +ℝ Path.derivativeAtZero signedLaws g

open LinearSignedPathDerivativeLaws public

pathFirstVariationLinearity :
  ∀ {carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier}
    (laws : LinearSignedPathDerivativeLaws)
    (sourcePath :
      Source.Background (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier) → ℝ →
      Source.Background (Carrier.source carrier)) →
  D1.FirstVariationLinearity
    (Source.Background (Carrier.source carrier))
    (Source.Tangent (Carrier.source carrier))
pathFirstVariationLinearity laws sourcePath = record
  { D1.FirstVariationLinearity.firstVariation =
      PathBC2.pathFirstVariation (signedLaws laws) sourcePath
  ; D1.FirstVariationLinearity.firstVariationCong =
      λ f g pointwise background tangent →
        Path.derivativeCong (signedLaws laws)
          (λ t → f (sourcePath background tangent t))
          (λ t → g (sourcePath background tangent t))
          (λ t → pointwise (sourcePath background tangent t))
  ; D1.FirstVariationLinearity.zeroFirstVariation =
      λ background tangent → derivativeZero laws
  ; D1.FirstVariationLinearity.addFirstVariation =
      λ f g background tangent →
        derivativeAdd laws
          (λ t → f (sourcePath background tangent t))
          (λ t → g (sourcePath background tangent t))
  }

round143LinearityIsPathDerivativeAlgebra : Bool
round143LinearityIsPathDerivativeAlgebra = true

noPhysicalSourceLeafInFirstVariationLinearity : Bool
noPhysicalSourceLeafInFirstVariationLinearity = true

standardOneVariableDerivativeLinearityIsSufficient : Bool
standardOneVariableDerivativeLinearityIsSufficient = true
