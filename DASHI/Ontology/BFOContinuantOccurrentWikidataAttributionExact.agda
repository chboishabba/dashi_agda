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

------------------------------------------------------------------------
-- Literal BFO -> Wikidata attribution control.
--
-- Source snapshot:
--   Basic Formal Ontology (BFO 2020), OWL 2 direct-semantics source.
--   BFO-ontology/BFO-2020 master commit
--   0900316ea9d330f599bd110f7f6504ed33a87fc8 (2026-08-16).
--   The source states:
--     BFO_0000002 continuant  rdfs:subClassOf BFO_0000001 entity
--     BFO_0000002 continuant  owl:disjointWith BFO_0000003 occurrent.
--   Standard context: ISO/IEC 21838-2:2021, Basic Formal Ontology (BFO).
--   No DOI is asserted for the source TTL/standard artifact.
--
-- Wikidata mapping surface checked for this tranche:
--   entity     Q35120     -> P12602 0000001
--   continuant Q103940464 -> P12602 0000002
--   occurrent  Q67518978  -> P12602 0000003
--
-- The live Mapping Wikidata To BFO project page says all BFO upper-ontology
-- classes have mappings while listing BFO-related constraints such as
-- continuant/occurrent disjointness as work to add.  Therefore the correct
-- certificate is NOT "Wikidata contradicts BFO".  Source and identifier
-- transcription are supported; disjointness transport remains unresolved until
-- the target disjointness + instance-transport hypotheses are established.
------------------------------------------------------------------------

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
bfoContinuantOccurrentCase =
  pinnedBFOContinuantOccurrentCase
    "0900316ea9d330f599bd110f7f6504ed33a87fc8"
    "BFO_0000001"
    "BFO_0000002"
    "BFO_0000003"
    "Q35120"
    "Q103940464"
    "Q67518978"
    "P12602"
    "Wikidata:WikiProject_Ontology/Mapping_Wikidata_To_BFO oldid=2412374796"

bfoDisjointnessTransportClaim : Fibre.ClaimBase
bfoDisjointnessTransportClaim =
  Fibre.claimBase
    "bfo-wikidata:continuant-occurrent-disjointness"
    "BFO continuant/occurrent disjointness is licensed for transport through the declared Wikidata alignment"
    (Fibre.externalClaimKind "BFO-Wikidata alignment")
    Fibre.candidateLinkRole
    "bfo:0900316e|wikidata:bfo-mapping:2412374796"

bfoContinuantOccurrentAttribution :
  Attribution.AttributedDerivationFibre bfoDisjointnessTransportClaim
bfoContinuantOccurrentAttribution =
  Attribution.attributedDerivationFibre
    (Attribution.mkAttributedDerivation
      bfoDisjointnessTransportClaim
      Attribution.sourceOntologyLayer
      Fibre.supporting
      "BFO 2020 source explicitly states continuant disjointWith occurrent"
      "BFO-2020:bfo-core.ttl@0900316ea9d330f599bd110f7f6504ed33a87fc8")
    (Attribution.mkAttributedDerivation
      bfoDisjointnessTransportClaim
      Attribution.transcriptionLayer
      Fibre.supporting
      "P12602 identifies entity/continuant/occurrent with BFO 0000001/2/3"
      "Wikidata:P12602 mapping surface; retrieved 2026-08-18")
    (Attribution.mkAttributedDerivation
      bfoDisjointnessTransportClaim
      Attribution.alignmentLayer
      Fibre.unresolved
      "no source-native instance-transport witness is supplied for disjoint_reflect"
      "JMD:Wikidata.Alignment.disjoint_reflect obligation")
    (Attribution.mkAttributedDerivation
      bfoDisjointnessTransportClaim
      Attribution.targetGraphLayer
      Fibre.unresolved
      "target-side continuant/occurrent disjointness constraint is not promoted from project intent to checked graph fact"
      "Wikidata BFO project page keeps related constraints as a work item")

bfoSourceAxisSupported :
  Square.squareOutcome
    (Attribution.attributedSquare
      (Attribution.sourceEvidence bfoContinuantOccurrentAttribution))
  ≡ Fibre.satisfied
bfoSourceAxisSupported = refl

bfoTranscriptionAxisSupported :
  Square.squareOutcome
    (Attribution.attributedSquare
      (Attribution.transcriptionEvidence bfoContinuantOccurrentAttribution))
  ≡ Fibre.satisfied
bfoTranscriptionAxisSupported = refl

bfoAlignmentAxisUndetermined :
  Square.squareOutcome
    (Attribution.attributedSquare
      (Attribution.alignmentEvidence bfoContinuantOccurrentAttribution))
  ≡ Fibre.undetermined
bfoAlignmentAxisUndetermined = refl

bfoTargetAxisUndetermined :
  Square.squareOutcome
    (Attribution.attributedSquare
      (Attribution.targetEvidence bfoContinuantOccurrentAttribution))
  ≡ Fibre.undetermined
bfoTargetAxisUndetermined = refl

bfoAlignmentMissingIsNeitherNotRefutation :
  Four.polarPosition
    (Attribution.attributedSquare
      (Attribution.alignmentEvidence bfoContinuantOccurrentAttribution))
  ≡ Tetralemma.neither
bfoAlignmentMissingIsNeitherNotRefutation = refl

bfoRequiredAlignmentSubfibreIsUndetermined :
  Fibre.validateRequiredSubfibre Fibre.axisRequired false false
  ≡ Fibre.fibreShape Fibre.undetermined
bfoRequiredAlignmentSubfibreIsUndetermined = refl

------------------------------------------------------------------------
-- Inference-language consequence.
--
-- Identifier/subclass alignment may be usable for a weaker query while the
-- stronger disjointness language is not yet licensed.  Missing transport is an
-- obligation, not evidence that BFO and Wikidata disagree.
------------------------------------------------------------------------

bfoMappingSubclassProfile : Language.AlignmentInferenceProfile
bfoMappingSubclassProfile = Language.subclassOnlyAlignment

bfoMappingCanServeSubclassLanguage :
  Language.safeFor bfoMappingSubclassProfile Language.subclassLanguage ≡ true
bfoMappingCanServeSubclassLanguage = refl

bfoMappingNotYetLicensedForDisjointnessLanguage :
  Language.safeFor bfoMappingSubclassProfile Language.disjointnessLanguage ≡ false
bfoMappingNotYetLicensedForDisjointnessLanguage = refl
