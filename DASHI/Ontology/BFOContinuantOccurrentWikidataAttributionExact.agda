module DASHI.Ontology.BFOContinuantOccurrentWikidataAttributionExact where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Algebra.TetralemmaBridge as Tetralemma
import DASHI.Interop.WikidataDerivationFibreBridge as Fibre
import DASHI.Interop.WikidataDerivationSupportSquareExact as Square
import DASHI.Ontology.CrossOntologyContradictionAttributionExact as Attribution
import DASHI.Ontology.InferenceLanguageIndexedAlignmentSafetyExact as Language

record PinnedBFOContinuantOccurrentCase : Set where
  constructor pinnedBFOContinuantOccurrentCase
  field
    sourceCommit : String
    sourceEntityId : String
    sourceContinuantId : String
    sourceOccurrentId : String
    targetEntityQid : String
    targetContinuantQid : String
    targetOccurrentQid : String
    targetIdentifierProperty : String
    wikidataProjectRevision : String
open PinnedBFOContinuantOccurrentCase public

bfoContinuantOccurrentCase : PinnedBFOContinuantOccurrentCase
bfoContinuantOccurrentCase = pinnedBFOContinuantOccurrentCase
  "0900316ea9d330f599bd110f7f6504ed33a87fc8"
  "BFO_0000001" "BFO_0000002" "BFO_0000003"
  "Q35120" "Q103940464" "Q67518978" "P12602"
  "Wikidata:WikiProject_Ontology/Mapping_Wikidata_To_BFO oldid=2412374796"

bfoDisjointnessTransportClaim : Fibre.ClaimBase
bfoDisjointnessTransportClaim = Fibre.claimBase
  "bfo-wikidata:continuant-occurrent-disjointness"
  "BFO continuant/occurrent disjointness is licensed for transport through the declared Wikidata alignment"
  (Fibre.externalClaimKind "BFO-Wikidata alignment")
  Fibre.candidateLinkRole
  "bfo:0900316e|wikidata:bfo-mapping:2412374796"

bfoContinuantOccurrentAttribution : Attribution.AttributedDerivationFibre bfoDisjointnessTransportClaim
bfoContinuantOccurrentAttribution = Attribution.attributedDerivationFibre
  (Attribution.mkAttributedDerivation bfoDisjointnessTransportClaim Attribution.sourceOntologyLayer Fibre.supporting
    "BFO 2020 source explicitly states continuant disjointWith occurrent"
    "BFO-2020:bfo-core.ttl@0900316ea9d330f599bd110f7f6504ed33a87fc8")
  (Attribution.mkAttributedDerivation bfoDisjointnessTransportClaim Attribution.transcriptionLayer Fibre.supporting
    "P12602 identifies entity/continuant/occurrent with BFO 0000001/2/3"
    "Wikidata:P12602 mapping surface; retrieved 2026-08-18")
  (Attribution.mkAttributedDerivation bfoDisjointnessTransportClaim Attribution.alignmentLayer Fibre.unresolved
    "no source-native instance-transport witness is supplied for disjoint_reflect"
    "JMD:Wikidata.Alignment.disjoint_reflect obligation")
  (Attribution.mkAttributedDerivation bfoDisjointnessTransportClaim Attribution.targetGraphLayer Fibre.unresolved
    "target-side continuant/occurrent disjointness constraint is not promoted from project intent to checked graph fact"
    "Wikidata BFO project page keeps related constraints as a work item")

bfoSourceAxisSupported :
  Square.squareOutcome (Attribution.attributedSquare (Attribution.sourceEvidence bfoContinuantOccurrentAttribution)) ≡ Fibre.satisfied
bfoSourceAxisSupported = refl

bfoTranscriptionAxisSupported :
  Square.squareOutcome (Attribution.attributedSquare (Attribution.transcriptionEvidence bfoContinuantOccurrentAttribution)) ≡ Fibre.satisfied
bfoTranscriptionAxisSupported = refl

bfoAlignmentAxisUndetermined :
  Square.squareOutcome (Attribution.attributedSquare (Attribution.alignmentEvidence bfoContinuantOccurrentAttribution)) ≡ Fibre.undetermined
bfoAlignmentAxisUndetermined = refl

bfoTargetAxisUndetermined :
  Square.squareOutcome (Attribution.attributedSquare (Attribution.targetEvidence bfoContinuantOccurrentAttribution)) ≡ Fibre.undetermined
bfoTargetAxisUndetermined = refl

bfoAlignmentMissingIsNeitherNotRefutation :
  Four.polarPosition (Attribution.attributedSquare (Attribution.alignmentEvidence bfoContinuantOccurrentAttribution)) ≡ Tetralemma.neither
bfoAlignmentMissingIsNeitherNotRefutation = refl

bfoMappingSubclassProfile : Language.AlignmentInferenceProfile
bfoMappingSubclassProfile = Language.subclassOnlyAlignment

bfoMappingCanServeSubclassLanguage :
  Language.safeFor bfoMappingSubclassProfile Language.subclassLanguage ≡ true
bfoMappingCanServeSubclassLanguage = refl

bfoMappingNotYetLicensedForDisjointnessLanguage :
  Language.safeFor bfoMappingSubclassProfile Language.disjointnessLanguage ≡ false
bfoMappingNotYetLicensedForDisjointnessLanguage = refl
