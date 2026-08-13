module DASHI.Cognition.PNF.OpticalTextCompressionPNFExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCES
--
-- Haoran Wei, Yaofeng Sun, Yukun Li,
-- "DeepSeek-OCR: Contexts Optical Compression",
-- arXiv:2510.18234 (2025), arXiv DOI 10.48550/arXiv.2510.18234.
--
-- Yanhong Li, Zixuan Lan, Jiawei Zhou,
-- "Text or Pixels? Evaluating Efficiency and Understanding of LLMs with
-- Visual Text Inputs", Findings of EMNLP 2025,
-- DOI 10.18653/v1/2025.findings-emnlp.558.
--
-- The sources motivate text-as-image / optical context compression.  The
-- finite model below proves only the PNF distinction between representation
-- modality, current surface reconstruction, and future/provenance sufficiency.
------------------------------------------------------------------------

deepSeekOCRTitle : String
deepSeekOCRTitle = "DeepSeek-OCR: Contexts Optical Compression"

deepSeekOCRAuthors : String
deepSeekOCRAuthors = "Haoran Wei; Yaofeng Sun; Yukun Li"

deepSeekOCRArXivDOI : String
deepSeekOCRArXivDOI = "10.48550/arXiv.2510.18234"

textOrPixelsTitle : String
textOrPixelsTitle = "Text or Pixels? Evaluating Efficiency and Understanding of LLMs with Visual Text Inputs"

textOrPixelsAuthors : String
textOrPixelsAuthors = "Yanhong Li; Zixuan Lan; Jiawei Zhou"

textOrPixelsDOI : String
textOrPixelsDOI = "10.18653/v1/2025.findings-emnlp.558"

------------------------------------------------------------------------
-- Modality is a representation/process coordinate, not semantic authority.
------------------------------------------------------------------------

data RepresentationModality : Set where
  textModality visualModality latentModality : RepresentationModality

data SurfaceText : Set where
  sameRenderedSentence : SurfaceText

data Provenance : Set where
  sourceA sourceB : Provenance

record FineTextState : Set where
  constructor fineTextState
  field
    surface : SurfaceText
    provenance : Provenance

open FineTextState public

data VisionCode : Set where
  renderedPageCode : VisionCode

textLeft textRight : FineTextState
textLeft = fineTextState sameRenderedSentence sourceA
textRight = fineTextState sameRenderedSentence sourceB

-- Optical encoding retains only the rendered surface in this toy carrier.
opticalEncode : FineTextState → VisionCode
opticalEncode state = renderedPageCode

opticalDecodeSurface : VisionCode → SurfaceText
opticalDecodeSurface renderedPageCode = sameRenderedSentence

surfaceReconstructionExact :
  (state : FineTextState) →
  opticalDecodeSurface (opticalEncode state) ≡ surface state
surfaceReconstructionExact (fineTextState sameRenderedSentence sourceA) = refl
surfaceReconstructionExact (fineTextState sameRenderedSentence sourceB) = refl

sameVisionCodeDespiteDifferentProvenance :
  opticalEncode textLeft ≡ opticalEncode textRight
sameVisionCodeDespiteDifferentProvenance = refl

provenanceDistinguishesFineStates :
  provenance textLeft ≡ provenance textRight → ⊥
provenanceDistinguishesFineStates ()

------------------------------------------------------------------------
-- Current OCR/surface fidelity is therefore weaker than fine PNF reopening.
------------------------------------------------------------------------

data ConsumerQuery : Set where
  askSurface askProvenance : ConsumerQuery

data ConsumerObservation : Set where
  surfaceObserved sourceAObserved sourceBObserved : ConsumerObservation

observeFine : ConsumerQuery → FineTextState → ConsumerObservation
observeFine askSurface state = surfaceObserved
observeFine askProvenance (fineTextState surface sourceA) = sourceAObserved
observeFine askProvenance (fineTextState surface sourceB) = sourceBObserved

currentSurfaceConsumerCannotDistinguish :
  observeFine askSurface textLeft ≡ observeFine askSurface textRight
currentSurfaceConsumerCannotDistinguish = refl

futureProvenanceConsumerDoesDistinguish :
  observeFine askProvenance textLeft ≡ observeFine askProvenance textRight → ⊥
futureProvenanceConsumerDoesDistinguish ()

perfectSurfaceReconstructionDoesNotImplyFineFutureSafety :
  opticalEncode textLeft ≡ opticalEncode textRight
  × (observeFine askProvenance textLeft ≡ observeFine askProvenance textRight → ⊥)
perfectSurfaceReconstructionDoesNotImplyFineFutureSafety =
  refl , futureProvenanceConsumerDoesDistinguish

------------------------------------------------------------------------
-- A provenance residual restores the fine carrier exactly.
------------------------------------------------------------------------

provenanceResidual : FineTextState → Provenance
provenanceResidual = provenance

reopenOpticalCode : VisionCode → Provenance → FineTextState
reopenOpticalCode renderedPageCode source =
  fineTextState sameRenderedSentence source

reopenOpticalWithProvenanceExact :
  (state : FineTextState) →
  reopenOpticalCode (opticalEncode state) (provenanceResidual state) ≡ state
reopenOpticalWithProvenanceExact (fineTextState sameRenderedSentence sourceA) = refl
reopenOpticalWithProvenanceExact (fineTextState sameRenderedSentence sourceB) = refl

------------------------------------------------------------------------
-- Representation-phase statement: a modality change may preserve the current
-- consumer invariant while changing the physical/token carrier.  It is not a
-- semantic phase transition unless the evidence/consumer relation changes.
------------------------------------------------------------------------

record ModalityReencoding : Set where
  constructor modalityReencoding
  field
    sourceModality : RepresentationModality
    targetModality : RepresentationModality
    preservesSurface : (state : FineTextState) →
      opticalDecodeSurface (opticalEncode state) ≡ surface state

open ModalityReencoding public

canonicalTextToVisualReencoding : ModalityReencoding
canonicalTextToVisualReencoding =
  modalityReencoding textModality visualModality surfaceReconstructionExact

------------------------------------------------------------------------
-- Boundary: strong OCR or benchmark compression evidence is not promoted to a
-- universal theorem that the optical code preserves every semantic, causal,
-- provenance, or future-query distinction in the fine carrier.
------------------------------------------------------------------------
