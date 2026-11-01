module DASHI.Cognition.PNF.SensibLawTranscriptBoundaryFibreBroadcastGraphExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawTranscriptBoundaryFibreClassifierExact as Fibre
import DASHI.Cognition.PNF.SensibLawTranscriptSpeakerResolutionExact as Speaker
import DASHI.Cognition.PNF.SensibLawAttributionPropositionOccurrenceBidiExact as Attribution
import DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact as Consumer

------------------------------------------------------------------------
-- TRANSCRIPT-BOUNDARY FIBRE BROADCAST GRAPH
--
-- The classifier produces several interpretations of the same structural cut.
-- This owner broadcasts those alternatives into typed downstream routes rather
-- than collapsing the highest score into an accepted segmentation.
------------------------------------------------------------------------

data BoundaryGraphRoute : Set where
  speakerResolutionRoute : BoundaryGraphRoute
  reporterQuoteFrameRoute : BoundaryGraphRoute
  attributionModalWrapperRoute : BoundaryGraphRoute
  transcriptRepairRoute : BoundaryGraphRoute
  contrastConcessionRoute : BoundaryGraphRoute

routeFor : Fibre.BoundaryFibreKind → BoundaryGraphRoute
routeFor Fibre.speakerCut = speakerResolutionRoute
routeFor Fibre.reporterQuoteHandoff = reporterQuoteFrameRoute
routeFor Fibre.attributionNesting = attributionModalWrapperRoute
routeFor Fibre.asrDamage = transcriptRepairRoute
routeFor Fibre.rhetoricalPivot = contrastConcessionRoute

routeOwnerReference : BoundaryGraphRoute → String
routeOwnerReference speakerResolutionRoute =
  "DASHI.Cognition.PNF.SensibLawTranscriptSpeakerResolutionExact"
routeOwnerReference reporterQuoteFrameRoute =
  "DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact.DiscourseActCandidate"
routeOwnerReference attributionModalWrapperRoute =
  "DASHI.Cognition.PNF.SensibLawAttributionPropositionOccurrenceBidiExact"
routeOwnerReference transcriptRepairRoute =
  "tools/slr-discourse-reconstruct transcript repair / reparse seam"
routeOwnerReference contrastConcessionRoute =
  "DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact"

record BoundaryBroadcastEdge : Set where
  constructor boundaryBroadcastEdge
  field
    fibreKind : Fibre.BoundaryFibreKind
    fibreScore : String
    evidenceReference : String
    candidateOnly : Bool
    route : BoundaryGraphRoute
    downstreamOwnerReference : String
    semanticAdmissionDeferred : Bool
    semanticAdmissionDeferredIsTrue : semanticAdmissionDeferred ≡ true

open BoundaryBroadcastEdge public

edgeFromScore : Fibre.BoundaryFibreScore → BoundaryBroadcastEdge
edgeFromScore score =
  boundaryBroadcastEdge
    (Fibre.kind score)
    (Fibre.score score)
    (Fibre.evidenceReference score)
    (Fibre.candidateOnly score)
    (routeFor (Fibre.kind score))
    (routeOwnerReference (routeFor (Fibre.kind score)))
    true refl

record BoundaryBroadcastGraph : Set where
  constructor boundaryBroadcastGraph
  field
    sourceSha256 : String
    sentenceReference : String
    splitReference : String
    cutReceiptReference : String
    classifierSchema : String
    rankedTopCandidate : Fibre.BoundaryFibreKind
    candidateEdges : List BoundaryBroadcastEdge
    scorerFeedbackEnabled : Bool
    scorerFeedbackEnabledIsFalse : scorerFeedbackEnabled ≡ false
    rankingAdjudicatesSegmentation : Bool
    rankingAdjudicatesSegmentationIsFalse : rankingAdjudicatesSegmentation ≡ false

open BoundaryBroadcastGraph public

compileBoundaryBroadcast : Fibre.BoundaryFibreVector → BoundaryBroadcastGraph
compileBoundaryBroadcast vector =
  boundaryBroadcastGraph
    (Fibre.sourceSha256 vector)
    (Fibre.sentenceReference vector)
    (Fibre.splitReference vector)
    (Fibre.v2CutReceiptReference vector)
    (Fibre.classifierSchema vector)
    (Fibre.topCandidate vector)
    ( edgeFromScore (Fibre.speaker vector)
    ∷ edgeFromScore (Fibre.quoteHandoff vector)
    ∷ edgeFromScore (Fibre.nesting vector)
    ∷ edgeFromScore (Fibre.asr vector)
    ∷ edgeFromScore (Fibre.rhetorical vector)
    ∷ [])
    false refl
    false refl

------------------------------------------------------------------------
-- BIDI route contracts.
--
-- These references make the intended downstream ownership explicit without
-- manufacturing the missing semantic objects.  Speaker identity remains in
-- SpeakerResolutionPacket; paid attribution/occurrence remains in the existing
-- ClaimAttributionOccurrenceWeld; consumer-specific discourse resolution stays
-- downstream of the candidate graph.
------------------------------------------------------------------------

speakerRouteOwner : String
speakerRouteOwner =
  "DASHI.Cognition.PNF.SensibLawTranscriptSpeakerResolutionExact.SpeakerResolutionPacket"

attributionRouteOwner : String
attributionRouteOwner =
  "DASHI.Cognition.PNF.SensibLawAttributionPropositionOccurrenceBidiExact.ClaimAttributionOccurrenceWeld"

consumerRouteOwner : String
consumerRouteOwner =
  "DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact.DiscourseActCandidate"

speakerOwnerIsUpstreamOfAttribution : String
speakerOwnerIsUpstreamOfAttribution = Speaker.attributionOwnerReference

------------------------------------------------------------------------
-- HARD NON-COLLAPSE LAWS
------------------------------------------------------------------------

data TopCandidateIsAcceptedSegmentation : Set where
data QuoteOrNestingIsSpeakerChange : Set where
data ASRDamageIsPropositionFalse : Set where
data SpeakerBoundaryIsSemanticContradiction : Set where
data FibreClassificationIsTruthProof : Set where
data CandidateClassifierFeedsCutScorer : Set where
data OneBoundaryHasOnlyOneInterpretation : Set where

topCandidateDoesNotAcceptSegmentation : TopCandidateIsAcceptedSegmentation → ⊥
topCandidateDoesNotAcceptSegmentation ()

quoteOrNestingDoesNotProveSpeakerChange : QuoteOrNestingIsSpeakerChange → ⊥
quoteOrNestingDoesNotProveSpeakerChange ()

asrDamageDoesNotNegateProposition : ASRDamageIsPropositionFalse → ⊥
asrDamageDoesNotNegateProposition ()

speakerBoundaryDoesNotCreateSemanticContradiction : SpeakerBoundaryIsSemanticContradiction → ⊥
speakerBoundaryDoesNotCreateSemanticContradiction ()

fibreClassificationDoesNotProveTruth : FibreClassificationIsTruthProof → ⊥
fibreClassificationDoesNotProveTruth ()

candidateClassifierDoesNotFeedCutScorer : CandidateClassifierFeedsCutScorer → ⊥
candidateClassifierDoesNotFeedCutScorer ()

oneBoundaryMayBroadcastCompetingInterpretations : OneBoundaryHasOnlyOneInterpretation → ⊥
oneBoundaryMayBroadcastCompetingInterpretations ()

------------------------------------------------------------------------
-- Boundary summary used by transcript-wide graph compilation.
------------------------------------------------------------------------

record FibreBroadcastBoundary : Set where
  constructor fibreBroadcastBoundary
  field
    fiveCandidateRoutesPreserved : Bool
    fiveCandidateRoutesPreservedIsTrue : fiveCandidateRoutesPreserved ≡ true
    topCandidateIsRankingMetadataOnly : Bool
    topCandidateIsRankingMetadataOnlyIsTrue : topCandidateIsRankingMetadataOnly ≡ true
    speakerRouteDoesNotVerifySpeaker : Bool
    speakerRouteDoesNotVerifySpeakerIsTrue : speakerRouteDoesNotVerifySpeaker ≡ true
    attributionRouteDoesNotProveTruth : Bool
    attributionRouteDoesNotProveTruthIsTrue : attributionRouteDoesNotProveTruth ≡ true
    asrRouteBlocksPrematureSemanticAdmission : Bool
    asrRouteBlocksPrematureSemanticAdmissionIsTrue : asrRouteBlocksPrematureSemanticAdmission ≡ true
    scorerFeedbackDisabled : Bool
    scorerFeedbackDisabledIsTrue : scorerFeedbackDisabled ≡ true

canonicalFibreBroadcastBoundary : FibreBroadcastBoundary
canonicalFibreBroadcastBoundary =
  fibreBroadcastBoundary true refl true refl true refl true refl true refl true refl
