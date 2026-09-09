{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPublishedFlowToRegularEProjectionRound241Exact where

------------------------------------------------------------------------
-- ROUND241 / SOURCE-NATIVE COMPLETE DENSITY -> PREFERRED REGULAR-E PROJECTION
--
-- R218 already carries the literal CMP119 complete density at every scale and
-- identifies its rho coordinate with the beta-driven density sequence.  Hence
-- the preferred BC1 regular-E source coordinate is not an inversion of an
-- abstract density: it is the regularE field of that same source object.
--
-- R221's total regularEOfDensity map is stronger than the selected consumer.
-- We instantiate it scale-wise from completeDensityAt and separately retain the
-- same-density equality, so arbitrary non-selected Density values carry no
-- physical meaning and cannot be used as a source-authority shortcut.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanCMP119Section2CompleteDensityDictionaryExact as CMP119
import DASHI.Physics.YangMills.BalabanBetaDrivenSourceNativePublishedFlowRound218Exact as R218
import DASHI.Physics.YangMills.BalabanCMP119RegularESourceProjectionRound221Exact as R221

asRegularESourceProjection :
  ∀ {trajectory split inputs} →
  R218.BetaDrivenSourceNativePublishedFlowInputs
    {trajectory = trajectory} {split = split} inputs →
  R221.CMP119RegularESourceProjection inputs
asRegularESourceProjection source = record
  { R221.CMP119RegularESourceProjection.RegularTerm = R218.RegularTerm source
  ; R221.CMP119RegularESourceProjection.regularEOfDensity =
      λ scale _ → CMP119.regularE (R218.completeDensityAt source scale)
  ; R221.CMP119RegularESourceProjection.IsCMP119Section2RegularE =
      λ scale _ regular →
        regular ≡ CMP119.regularE (R218.completeDensityAt source scale)
  ; R221.CMP119RegularESourceProjection.selectedRegularEIsSourceCoordinate =
      λ _ → refl
  }

selectedRegularEIsLiteralPublishedRegularE :
  ∀ {trajectory split inputs}
    (source : R218.BetaDrivenSourceNativePublishedFlowInputs
      {trajectory = trajectory} {split = split} inputs) →
  ∀ scale →
  R221.selectedRegularE (asRegularESourceProjection source) scale
  ≡ CMP119.regularE (R218.completeDensityAt source scale)
selectedRegularEIsLiteralPublishedRegularE source scale = refl

publishedDensityIsSelectedBetaDensity :
  ∀ {trajectory split inputs}
    (source : R218.BetaDrivenSourceNativePublishedFlowInputs
      {trajectory = trajectory} {split = split} inputs) →
  ∀ scale →
  CMP119.rho (R218.completeDensityAt source scale)
  ≡ Beta.densityAt inputs scale
publishedDensityIsSelectedBetaDensity source scale =
  R218.densityIsBetaDensity source scale

selectedBetaDensityIsPublishedDensity :
  ∀ {trajectory split inputs}
    (source : R218.BetaDrivenSourceNativePublishedFlowInputs
      {trajectory = trajectory} {split = split} inputs) →
  ∀ scale →
  Beta.densityAt inputs scale
  ≡ CMP119.rho (R218.completeDensityAt source scale)
selectedBetaDensityIsPublishedDensity source scale =
  sym (publishedDensityIsSelectedBetaDensity source scale)

publishedFlowToRegularEProjectionCompilerLevel : ProofLevel
publishedFlowToRegularEProjectionCompilerLevel = machineChecked

-- The stronger source-native family is still the physical/source realization
-- premise.  Once supplied, R221's preferred regular-E source coordinate is
-- compiler output and must not be counted as another independent theorem.
literalBetaDrivenPublishedCompleteDensityFamilyLevel : ProofLevel
literalBetaDrivenPublishedCompleteDensityFamilyLevel =
  R218.literalBetaDrivenSourceNativePublishedFlowInputsLevel
