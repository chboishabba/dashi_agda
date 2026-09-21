module DASHI.Law.ReaderVisualisationPickParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.LegalVisualisationIRProjectionBoundaryExact as Visual

------------------------------------------------------------------------
-- S17: VisualisationIR is reader-owned transport; selection wraps one existing
-- ReaderIntent with a target coordinate.  DOM/GPU pick is therefore renderer
-- metadata, not a new semantic command or evidence-payment operation.
------------------------------------------------------------------------

data ReaderIntent : Set where
  explain whyClaim openSource expandProofCone back : ReaderIntent

record ReaderPickIntent : Set where
  constructor readerPickIntent
  field
    targetRef : String
    intent : ReaderIntent
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false
    createsEvidencePayment : Bool
    createsEvidencePaymentIsFalse :
      createsEvidencePayment ≡ false

open ReaderPickIntent public

dioxusPick : ReaderPickIntent
dioxusPick =
  readerPickIntent
    "mabo:proposition:radical-title-native-title"
    expandProofCone
    false refl
    false refl

gpuPick : ReaderPickIntent
gpuPick =
  readerPickIntent
    "mabo:proposition:radical-title-native-title"
    expandProofCone
    false refl
    false refl

dioxusGpuPickParity : dioxusPick ≡ gpuPick
dioxusGpuPickParity = refl

visualisationBoundary :
  Visual.LegalVisualisationIRBoundary
visualisationBoundary =
  Visual.canonicalLegalVisualisationIRBoundary

record ReaderVisualisationPickBoundary : Set where
  constructor readerVisualisationPickBoundary
  field
    visualisationTransportOwnedByReaderAbi : Bool
    visualisationTransportOwnedByReaderAbiIsTrue :
      visualisationTransportOwnedByReaderAbi ≡ true

    dioxusAndGpuPickMayCompileToSameReaderIntent : Bool
    dioxusAndGpuPickMayCompileToSameReaderIntentIsTrue :
      dioxusAndGpuPickMayCompileToSameReaderIntent ≡ true

    pickCreatesEvidencePayment : Bool
    pickCreatesEvidencePaymentIsFalse :
      pickCreatesEvidencePayment ≡ false

    pickCreatesSemanticAuthority : Bool
    pickCreatesSemanticAuthorityIsFalse :
      pickCreatesSemanticAuthority ≡ false

    rendererMayReconstructLegalSemanticsFromLayout : Bool
    rendererMayReconstructLegalSemanticsFromLayoutIsFalse :
      rendererMayReconstructLegalSemanticsFromLayout ≡ false

open ReaderVisualisationPickBoundary public

canonicalReaderVisualisationPickBoundary :
  ReaderVisualisationPickBoundary
canonicalReaderVisualisationPickBoundary =
  readerVisualisationPickBoundary
    true refl
    true refl
    false refl
    false refl
    false refl

data RendererLayoutAutomaticallySemanticCommand : Set where

rendererLayoutDoesNotBecomeSemanticCommand :
  RendererLayoutAutomaticallySemanticCommand → ⊥
rendererLayoutDoesNotBecomeSemanticCommand ()
