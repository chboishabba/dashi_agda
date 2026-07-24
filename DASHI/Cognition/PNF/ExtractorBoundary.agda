module DASHI.Cognition.PNF.ExtractorBoundary where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.EventAlgebra as PNF

record ASRHypothesis : Set where
  constructor asrHypothesis
  field
    surfaceText : String
    startTime endTime confidence : Nat
    candidatePNF : PNF.CandidatePNF

open ASRHypothesis public

record ASRLattice : Set where
  constructor asrLattice
  field
    hypotheses : List ASRHypothesis
    latticeReceipt : String
    collapsedBeforePNF : Bool
    collapsedBeforePNFIsFalse : collapsedBeforePNF ≡ false

open ASRLattice public

data TranslationResidual : Set where
  evidentialityLost honorificShift aspectUnderspecified : TranslationResidual
  legalTermNonCoextensive agentOmitted numberOrGenderAmbiguous : TranslationResidual
  noRecordedTranslationResidual : TranslationResidual

record TranslationTransport : Set where
  constructor translationTransport
  field
    sourceLanguage targetLanguage : String
    source target : PNF.EventPNF
    preservedInvariantLabels : List String
    residuals : List TranslationResidual
    transportReceipt : String

open TranslationTransport public

record SidecarSemanticCandidate : Set where
  constructor sidecarSemanticCandidate
  field
    producer : PNF.ParserProducer
    candidate : PNF.CandidatePNF
    alignedSpanReceipt : PNF.SpanReceipt
    documentedInferenceRule : String
    canonicalWithoutPNFResolution : Bool
    canonicalWithoutPNFResolutionIsFalse :
      canonicalWithoutPNFResolution ≡ false

open SidecarSemanticCandidate public

record ExtractorAuthorityBoundary : Set where
  constructor extractorAuthorityBoundary
  field
    spaCyOrStanzaIsCanonicalMeaning : Bool
    spaCyOrStanzaIsCanonicalMeaningIsFalse : spaCyOrStanzaIsCanonicalMeaning ≡ false
    amrUccaMrsMayBypassSpanReceipt : Bool
    amrUccaMrsMayBypassSpanReceiptIsFalse : amrUccaMrsMayBypassSpanReceipt ≡ false
    extractorMayDirectlyEmitDomainIR : Bool
    extractorMayDirectlyEmitDomainIRIsFalse : extractorMayDirectlyEmitDomainIR ≡ false

canonicalExtractorAuthorityBoundary : ExtractorAuthorityBoundary
canonicalExtractorAuthorityBoundary =
  extractorAuthorityBoundary false refl false refl false refl
