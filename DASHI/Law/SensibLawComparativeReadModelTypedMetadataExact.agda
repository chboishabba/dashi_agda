module DASHI.Law.SensibLawComparativeReadModelTypedMetadataExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawChangeLocusExact as Locus
import DASHI.Law.SensibLawTypedAnswerChangingExplanationExact as Explain
import DASHI.Law.SensibLawTypedWorkbenchTransportBoundaryExact as Transport

------------------------------------------------------------------------
-- M11.3 TYPED COMPARATIVE READ-MODEL METADATA
--
-- The UI receives the already-typed locus and its justification receipt.
-- Labels, geometry, colour and renderer class are presentation only and may
-- never be used to manufacture a ChangeLayer.
------------------------------------------------------------------------

record ComparativeReadModelAnnotation : Set where
  constructor comparative-read-model-annotation
  field
    semanticRef : String
    layer : Locus.ChangeLayer
    justificationRef : String
    explanationRef : String
    answerChanging : Bool
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse :
      createsClaimTruth ≡ false

open ComparativeReadModelAnnotation public

pabaiDefeaterReadModelAnnotation : ComparativeReadModelAnnotation
pabaiDefeaterReadModelAnnotation =
  comparative-read-model-annotation
    "coordinate:pabai:comparative:defeater"
    Locus.applicabilityLayer
    "receipt:reviewed-defeater"
    (Explain.explanationRef Explain.pabaiDefeaterStep)
    true
    true refl
    false refl
    false refl

pabaiCounterReadModelAnnotation : ComparativeReadModelAnnotation
pabaiCounterReadModelAnnotation =
  comparative-read-model-annotation
    "coordinate:pabai:comparative:counter-defeater"
    Locus.applicabilityLayer
    "receipt:reviewed-counter-distinction"
    (Explain.explanationRef Explain.pabaiCounterStep)
    true
    true refl
    false refl
    false refl

pabaiDefeaterLayerPreserved :
  layer pabaiDefeaterReadModelAnnotation ≡ Locus.applicabilityLayer
pabaiDefeaterLayerPreserved = refl

pabaiCounterLayerPreserved :
  layer pabaiCounterReadModelAnnotation ≡ Locus.applicabilityLayer
pabaiCounterLayerPreserved = refl

data UiLabelDeterminesChangeLayer : Set where
data RendererGeometryDeterminesChangeLayer : Set where
data MissingJustificationMayBeGuessed : Set where
data DisplayedAnnotationCreatesClaimTruth : Set where
data DisplayedAnnotationCreatesSemanticAuthority : Set where

uiLabelDoesNotDetermineChangeLayer :
  UiLabelDeterminesChangeLayer → ⊥
uiLabelDoesNotDetermineChangeLayer ()

rendererGeometryDoesNotDetermineChangeLayer :
  RendererGeometryDeterminesChangeLayer → ⊥
rendererGeometryDoesNotDetermineChangeLayer ()

missingJustificationRemainsUnresolved :
  MissingJustificationMayBeGuessed → ⊥
missingJustificationRemainsUnresolved ()

displayedAnnotationDoesNotCreateTruth :
  DisplayedAnnotationCreatesClaimTruth → ⊥
displayedAnnotationDoesNotCreateTruth ()

displayedAnnotationDoesNotCreateAuthority :
  DisplayedAnnotationCreatesSemanticAuthority → ⊥
displayedAnnotationDoesNotCreateAuthority ()

transportBoundary : Transport.TypedWorkbenchTransportBoundary
transportBoundary = Transport.canonicalTypedWorkbenchTransportBoundary

typedRustStillOwnsProductionCarrier :
  Transport.typedRustIsProductionWorkbenchCarrier transportBoundary ≡ true
typedRustStillOwnsProductionCarrier = refl

dioxusStillDoesNotOwnSemanticComparison :
  Transport.dioxusOwnsSemanticComparison transportBoundary ≡ false
dioxusStillDoesNotOwnSemanticComparison = refl

record ComparativeReadModelTypedMetadataBoundary : Set where
  constructor comparativeReadModelTypedMetadataBoundary
  field
    typedChangeLayerCarriedIntoReadModel : Bool
    typedChangeLayerCarriedIntoReadModelIsTrue :
      typedChangeLayerCarriedIntoReadModel ≡ true

    justificationReceiptCarriedIntoReadModel : Bool
    justificationReceiptCarriedIntoReadModelIsTrue :
      justificationReceiptCarriedIntoReadModel ≡ true

    answerChangingStatusCarriedIntoReadModel : Bool
    answerChangingStatusCarriedIntoReadModelIsTrue :
      answerChangingStatusCarriedIntoReadModel ≡ true

    uiMayInferChangeLayerFromLabels : Bool
    uiMayInferChangeLayerFromLabelsIsFalse :
      uiMayInferChangeLayerFromLabels ≡ false

    rendererMayInferChangeLayerFromGeometry : Bool
    rendererMayInferChangeLayerFromGeometryIsFalse :
      rendererMayInferChangeLayerFromGeometry ≡ false

    missingJustificationMayBeSilentlyFilled : Bool
    missingJustificationMayBeSilentlyFilledIsFalse :
      missingJustificationMayBeSilentlyFilled ≡ false

    presentationCreatesSemanticAuthority : Bool
    presentationCreatesSemanticAuthorityIsFalse :
      presentationCreatesSemanticAuthority ≡ false

    presentationCreatesClaimTruth : Bool
    presentationCreatesClaimTruthIsFalse :
      presentationCreatesClaimTruth ≡ false

open ComparativeReadModelTypedMetadataBoundary public

canonicalComparativeReadModelTypedMetadataBoundary :
  ComparativeReadModelTypedMetadataBoundary
canonicalComparativeReadModelTypedMetadataBoundary =
  comparativeReadModelTypedMetadataBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
