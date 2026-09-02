module DASHI.Cognition.PNF.SensibLawMaterialisedSpacyToOntologyVerticalExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact as Trace
import DASHI.Cognition.PNF.SensibLawAttributionPropositionOccurrenceBidiExact as Attribution
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Interop.SensibLawOntologyTopology as Ontology

------------------------------------------------------------------------
-- GENERIC PARSER/PNF -> ONTOLOGY PRODUCER ADAPTER
--
-- The input is already parser-derived candidate semantics.  Stable ontology
-- ids and source perspective are explicit inputs, not guessed from token text.
-- Constructing Event/Claim/Perspective does not establish truth or occurrence.
------------------------------------------------------------------------

record ParserSemanticOntologyInput : Set where
  constructor parserSemanticOntologyInput
  field
    predicateToken : Spacy.SpacyTokenObservation
    supportingTokens : List Spacy.SpacyTokenObservation
    semanticFibre : Candidate.CandidateSemanticFibre
    propositionFormula : Candidate.Formula
    eventId : Ontology.StableId
    eventClassId : Ontology.StableId
    claimId : Ontology.StableId
    perspectiveId : Ontology.StableId
    speakerId : Ontology.StableId
    eventDescription : String
    claimText : String
    frameLabel : String
    parserEvidenceReference : String
    semanticResolutionReference : String
    sourcePerspectiveReference : String
    parserAloneAuthorizesTruth : Bool
    parserAloneAuthorizesOccurrence : Bool

open ParserSemanticOntologyInput public

record ParserSemanticOntologyOutput (input : ParserSemanticOntologyInput) : Set where
  constructor parserSemanticOntologyOutput
  field
    event : Ontology.Event
    perspective : Ontology.Perspective
    claim : Ontology.Claim
    weld : Attribution.ClaimAttributionOccurrenceWeld claim perspective event
    parserTokenPreserved : Spacy.SpacyTokenObservation
    parserTokenPreservedExact : parserTokenPreserved ≡ predicateToken input
    sourceFibrePreserved : Candidate.CandidateSemanticFibre
    sourceFibrePreservedExact : sourceFibrePreserved ≡ semanticFibre input
    propositionFormulaPreserved : Candidate.Formula
    propositionFormulaPreservedExact : propositionFormulaPreserved ≡ propositionFormula input

open ParserSemanticOntologyOutput public

compileParserSemanticOntology :
  (input : ParserSemanticOntologyInput) →
  ParserSemanticOntologyOutput input
compileParserSemanticOntology input =
  parserSemanticOntologyOutput
    eventValue
    perspectiveValue
    claimValue
    (Attribution.canonicalClaimAttributionOccurrenceWeld
      claimValue perspectiveValue eventValue refl refl)
    (predicateToken input)
    refl
    (semanticFibre input)
    refl
    (propositionFormula input)
    refl
  where
    eventValue : Ontology.Event
    eventValue =
      Ontology.event
        (eventId input)
        (eventClassId input)
        "occurrence-unresolved"
        (eventDescription input)

    perspectiveValue : Ontology.Perspective
    perspectiveValue =
      Ontology.perspectiveRecord
        (perspectiveId input)
        (speakerId input)
        (frameLabel input)

    claimValue : Ontology.Claim
    claimValue =
      Ontology.claimRecord
        (claimId input)
        (eventId input)
        (speakerId input)
        (claimText input)
        (perspectiveId input)

------------------------------------------------------------------------
-- MATERIALISED README SPACY SPECIMEN
--
-- Trace.candidateFibre and Trace.finalFormula come from the real en_core_web_sm
-- parse fixture in SpacyNegatedCoordinationScopeTraceExact.
------------------------------------------------------------------------

readmeInput : ParserSemanticOntologyInput
readmeInput =
  parserSemanticOntologyInput
    Trace.mutateToken
    (Trace.itToken ∷ Trace.notToken ∷ Trace.stateToken ∷ Trace.promoteToken
      ∷ Trace.tasksToken ∷ Trace.itselfToken ∷ [])
    Trace.candidateFibre
    Trace.finalFormula
    (Ontology.stableId "event:spacy-readme:mutate-promote:1")
    (Ontology.stableId "event-class:runtime-state-transition")
    (Ontology.stableId "claim:spacy-readme:negated-runtime-transition:1")
    (Ontology.stableId "perspective:sensiblaw-readme:source")
    (Ontology.stableId "speaker:sensiblaw-readme:source")
    "candidate runtime mutation/promotion eventuality from materialised spaCy trace"
    Trace.sourceSentence
    "source-document perspective; attribution supplied by document provenance"
    "SpacyNegatedCoordinationScopeTraceExact materialised en_core_web_sm parse"
    "reviewed candidate PNF from materialised trace; scope history retained"
    "source perspective supplied by document provenance, not parser lexical inference"
    false
    false

readmeOutput : ParserSemanticOntologyOutput readmeInput
readmeOutput = compileParserSemanticOntology readmeInput

readmeEvent : Ontology.Event
readmeEvent = event readmeOutput

readmeClaim : Ontology.Claim
readmeClaim = claim readmeOutput

readmePerspective : Ontology.Perspective
readmePerspective = perspective readmeOutput

readmeEventSameLiteralParserSemanticId :
  Ontology.Event.eventId readmeEvent
  ≡ Ontology.stableId "event:spacy-readme:mutate-promote:1"
readmeEventSameLiteralParserSemanticId = refl

readmeClaimAboutSameEvent :
  Ontology.Claim.aboutEvent readmeClaim ≡ Ontology.Event.eventId readmeEvent
readmeClaimAboutSameEvent = refl

readmeClaimSameSpeakerAsPerspective :
  Ontology.Claim.assertedBy readmeClaim
  ≡ Ontology.Perspective.speakerId readmePerspective
readmeClaimSameSpeakerAsPerspective = refl

readmeParserFibrePreserved :
  sourceFibrePreserved readmeOutput ≡ Trace.candidateFibre
readmeParserFibrePreserved = refl

readmeParserFormulaPreserved :
  propositionFormulaPreserved readmeOutput ≡ Trace.finalFormula
readmeParserFormulaPreserved = refl

------------------------------------------------------------------------
-- The ontology weld intentionally begins at assertion/mention, never truth or
-- occurrence admission.  The historical Event.occurredAt field is populated
-- with an explicit unresolved marker and carries no semantic authority.
------------------------------------------------------------------------

readmeClaimStartsTruthUnresolved :
  Status.truthStatus (Attribution.proposition (weld readmeOutput))
  ≡ Status.truthUnresolved
readmeClaimStartsTruthUnresolved = refl

readmeEventStartsMentionedOnly :
  Status.occurrence (Attribution.occurrence (weld readmeOutput))
  ≡ Status.mentionedEventuality
readmeEventStartsMentionedOnly = refl

readmeOccurredAtIsExplicitlyUnresolved :
  Ontology.Event.occurredAt readmeEvent ≡ "occurrence-unresolved"
readmeOccurredAtIsExplicitlyUnresolved = refl

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data ParserSemanticFibreAutomaticallyTruth : Set where
data ParserSemanticFibreAutomaticallyOccurrence : Set where
data OntologyEventRecordMeansOccurred : Set where
data ParserTokenTextAutomaticallySpeaker : Set where

parserSemanticFibreDoesNotProveTruth :
  ParserSemanticFibreAutomaticallyTruth → ⊥
parserSemanticFibreDoesNotProveTruth ()

parserSemanticFibreDoesNotProveOccurrence :
  ParserSemanticFibreAutomaticallyOccurrence → ⊥
parserSemanticFibreDoesNotProveOccurrence ()

ontologyEventRecordDoesNotProveOccurrence :
  OntologyEventRecordMeansOccurred → ⊥
ontologyEventRecordDoesNotProveOccurrence ()

parserTokenTextDoesNotChooseSpeaker :
  ParserTokenTextAutomaticallySpeaker → ⊥
parserTokenTextDoesNotChooseSpeaker ()
