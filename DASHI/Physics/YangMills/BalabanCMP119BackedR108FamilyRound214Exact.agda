{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119BackedR108FamilyRound214Exact where

------------------------------------------------------------------------
-- ROUND214 / CMP119 SOURCE REPRESENTATION -> SOURCE-FIXED R108 FAMILY
--
-- Once the CMP119 complete-density representation supplies its own A_k
-- effective-action projection, the R108 family must consume that projection
-- literally.  This module leaves only the source localization data as inputs;
-- it never accepts another Density -> Potential map.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Flow
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Radius
import DASHI.Physics.YangMills.BalabanCMP119DensityEffectiveActionProjectionRound214Exact as CMP119
import DASHI.Physics.YangMills.BalabanSourceFixedR108EffectiveActionFamilyRound213Exact as Fixed
import DASHI.Physics.YangMills.BalabanBetaDrivenDensityToCMP109116CarrierRound108Exact as R108

record CMP119BackedR108LocalizationData
    {trajectory split}
    {inputs : Flow.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    (representation : CMP119.CMP119CompleteDensityActionRepresentation inputs)
    : Set₁ where
  field
    Volume Tangent Component : Set

    components : Nat → Volume → List Component

    physicalLocalizedActivity :
      Nat → Volume → Component → CMP119.Background representation → ℝ

    selectedActionIsLocalizedCompositeSum :
      ∀ scale volume background →
      CMP119.selectedEffectiveAction representation scale background
      ≡ Finite.sumFunctions
          (Finite.mapList
            (physicalLocalizedActivity scale volume)
            (components scale volume))
          background

    commonRadius : Radius.CMP116CommonAnalyticRadius Nat Volume

open CMP119BackedR108LocalizationData public

asSourceFixedR108LocalizedFamily :
  ∀ {trajectory split inputs representation} →
  CMP119BackedR108LocalizationData
    {trajectory = trajectory} {split = split} {inputs = inputs} representation →
  Fixed.SourceFixedR108LocalizedFamily
    (CMP119.asFixedR108EffectiveDensitySemantics representation)
asSourceFixedR108LocalizedFamily {representation = representation} dataSet = record
  { Fixed.SourceFixedR108LocalizedFamily.Volume = Volume dataSet
  ; Fixed.SourceFixedR108LocalizedFamily.Tangent = Tangent dataSet
  ; Fixed.SourceFixedR108LocalizedFamily.Component = Component dataSet
  ; Fixed.SourceFixedR108LocalizedFamily.components = components dataSet
  ; Fixed.SourceFixedR108LocalizedFamily.physicalLocalizedActivity =
      physicalLocalizedActivity dataSet
  ; Fixed.SourceFixedR108LocalizedFamily.sourceDensityPotentialIsLocalizedCompositeSum =
      λ scale volume background →
        selectedActionIsLocalizedCompositeSum dataSet scale volume background
  ; Fixed.SourceFixedR108LocalizedFamily.commonRadius = commonRadius dataSet
  }

asR108Family :
  ∀ {trajectory split inputs representation} →
  CMP119BackedR108LocalizationData
    {trajectory = trajectory} {split = split} {inputs = inputs} representation →
  R108.BetaDrivenLocalizedEffectiveActionFamily inputs
asR108Family dataSet =
  Fixed.asR108LocalizedEffectiveActionFamily
    (asSourceFixedR108LocalizedFamily dataSet)

r108PotentialIsLiteralCMP119ActionProjection :
  ∀ {trajectory split inputs representation}
    (dataSet : CMP119BackedR108LocalizationData
      {trajectory = trajectory} {split = split} {inputs = inputs} representation) →
  ∀ density background →
  R108.potentialOfDensity (asR108Family dataSet) density background
  ≡ CMP119.effectiveActionOfDensity representation density background
r108PotentialIsLiteralCMP119ActionProjection dataSet density background = refl

r108SelectedPotentialIsLiteralCMP119ActionProjection :
  ∀ {trajectory split inputs representation}
    (dataSet : CMP119BackedR108LocalizationData
      {trajectory = trajectory} {split = split} {inputs = inputs} representation) →
  ∀ scale background →
  R108.potentialOfDensity (asR108Family dataSet)
      (Flow.densityAt inputs scale) background
  ≡ CMP119.selectedEffectiveAction representation scale background
r108SelectedPotentialIsLiteralCMP119ActionProjection dataSet scale background = refl

cmp119BackedR108FamilyCompilerLevel : ProofLevel
cmp119BackedR108FamilyCompilerLevel = machineChecked

cmp119ToR108PotentialSameObjectLevel : ProofLevel
cmp119ToR108PotentialSameObjectLevel = machineChecked

-- Source work: instantiate the localized activities and common analytic domain
-- from the literal CMP116 decomposition of the SAME CMP119 A_k coordinate.
literalCMP119BackedR108LocalizationLevel : ProofLevel
literalCMP119BackedR108LocalizationLevel = conditional
