{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFunctionalRegularEContinuationRound245Exact where

------------------------------------------------------------------------
-- ROUND245 / FUNCTION-VALUED REGULAR E + CMP119 LOCALIZATION -> CMP109/116
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFunctionalRegularESourceFlowRound242Exact as R242
import DASHI.Physics.YangMills.BalabanFunctionalFlowToRegularESemanticsRound243Exact as R243
import DASHI.Physics.YangMills.BalabanCMP119RegularELocalizationSourceRound244Exact as R244
import DASHI.Physics.YangMills.BalabanCMP119RegularEPreferredContinuationRound222Exact as R222
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Continue

asPreferredRegularERealization :
  ∀ {trajectory split inputs}
    (source : R242.FunctionalRegularESourceFlowInputs
      {trajectory = trajectory} {split = split} inputs)
    (localization : R244.CMP119RegularELocalizationCarrier source)
    (Tangent : Set) →
  R222.PreferredRegularERealization (R243.functionalProjection source)
asPreferredRegularERealization source localization Tangent = record
  { R222.PreferredRegularERealization.Background = R242.Background source
  ; R222.PreferredRegularERealization.Volume = R244.Volume localization
  ; R222.PreferredRegularERealization.Tangent = Tangent
  ; R222.PreferredRegularERealization.Component = R244.Component localization
  ; R222.PreferredRegularERealization.evaluateRegularE = λ regular → regular
  ; R222.PreferredRegularERealization.components = R244.components localization
  ; R222.PreferredRegularERealization.localizedRegularActivity =
      R244.localizedRegularActivity localization
  ; R222.PreferredRegularERealization.selectedRegularEIsLocalizedCompositeSum =
      R244.selectedRegularEIsLocalizedCompositeSum localization
  }

asCMP109116Continuation :
  ∀ {trajectory split inputs}
    (source : R242.FunctionalRegularESourceFlowInputs
      {trajectory = trajectory} {split = split} inputs)
    (localization : R244.CMP119RegularELocalizationCarrier source)
    (Tangent : Set) →
  Continue.CMP109116LiteralEffectiveActionContinuation
asCMP109116Continuation source localization Tangent =
  R222.asCMP109116Continuation
    (asPreferredRegularERealization source localization Tangent)

continuationPotentialIsLiteralRegularE :
  ∀ {trajectory split inputs}
    (source : R242.FunctionalRegularESourceFlowInputs
      {trajectory = trajectory} {split = split} inputs)
    (localization : R244.CMP119RegularELocalizationCarrier source)
    (Tangent : Set) →
  ∀ scale volume background →
  Continue.cmp109EffectivePotential
    (asCMP109116Continuation source localization Tangent)
    scale volume background
  ≡ R242.selectedRegularEFunction source scale background
continuationPotentialIsLiteralRegularE source localization Tangent scale volume background = refl

functionalRegularEContinuationCompilerLevel : ProofLevel
functionalRegularEContinuationCompilerLevel = machineChecked

literalFunctionalCMP119PublishedFlowLevel : ProofLevel
literalFunctionalCMP119PublishedFlowLevel = R242.literalFunctionalCMP119PublishedFlowLevel

literalCMP119RegularELocalizationCarrierLevel : ProofLevel
literalCMP119RegularELocalizationCarrierLevel = R244.literalCMP119RegularELocalizationCarrierLevel
