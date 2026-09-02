module DASHI.Cognition.PNF.SensibLawPdfReportingAttributionMaterialisedLiveExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.NumericAuthority as Authority
import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Cognition.PNF.SensibLawMaterialisedSpacyToOntologyVerticalExact as Compiler
import DASHI.Cognition.PNF.SensibLawAttributionPropositionOccurrenceBidiExact as Attribution
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Interop.SensibLawOntologyTopology as Ontology

------------------------------------------------------------------------
-- PDF-BACKED MATERIALISED REPORTING ATTRIBUTION VERTICAL
--
-- Source receipt:
--   sensiblaw.reporting-attribution-fixture.v0_1
--   text sha256 84eeb6e3b6900521796fd1d669b7f8b1998d652ce8fed0a98fc0486b01e2a01d
--
-- The paragraph was extracted from the Native Title (New South Wales) Act
-- 1994 (NSW) PDF fixture and parsed with en_core_web_sm.  This module retains
-- the exact sentence-local parser structure needed by the semantic consumer:
--
--   nsubj(submitted, applicant)
--   ccomp(submitted, conferred)
--   nsubj(conferred, grant)
--   dobj(conferred, right)
--
-- The Python harness used a lexical reporting-lemma set for discovery and a
-- convenience surface check for source_candidate.  Those are NOT semantic
-- authority here.  The Agda attribution is paid by the actual dependency
-- structure above.  The raw ccomp edge is retained under its literal name
-- because the older generic DependencyShape currently has no ccomp constructor.
------------------------------------------------------------------------

record ReportingFixtureProvenance : Set where
  constructor reportingFixtureProvenance
  field
    schemaVersion : String
    authority : String
    sourceReference : String
    textSha256 : String
    paragraphStart paragraphEnd paragraphSentences : Nat
    parserModelReference : String
    parserAloneAuthorizesTruth : Bool
    parserAloneAuthorizesTruthIsFalse : parserAloneAuthorizesTruth ≡ false
    parserAloneAuthorizesOccurrence : Bool
    parserAloneAuthorizesOccurrenceIsFalse :
      parserAloneAuthorizesOccurrence ≡ false
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    governedAdmissionPresent : Bool
    governedAdmissionPresentIsFalse : governedAdmissionPresent ≡ false

open ReportingFixtureProvenance public

fixtureProvenance : ReportingFixtureProvenance
fixtureProvenance =
  reportingFixtureProvenance
    "sensiblaw.reporting-attribution-fixture.v0_1"
    "parser_observation_and_candidate_status_only"
    "../ITIR-suite/SensibLaw/Native Title (New South Wales) Act 1994 (NSW).pdf"
    "84eeb6e3b6900521796fd1d669b7f8b1998d652ce8fed0a98fc0486b01e2a01d"
    0 515 3
    "spaCy en_core_web_sm; Rust semantic-status branch be53eebe97509814ae13f01e9b02440b2ce624ec"
    false refl
    false refl
    true refl
    false refl

sentenceId : Authority.SentenceId
sentenceId = Authority.sentenceId 1

sym : Nat → Authority.SymbolId
sym = Authority.symbolId

ann : Nat → Spacy.NumericAnnotation
ann n = Spacy.annotationPresent (sym n)

------------------------------------------------------------------------
-- Literal parser observations from sentence 1 of the receipt.  Numeric symbol
-- ids are local stable handles; source offsets, ordinals and heads are the
-- receipt coordinates that carry the parser identity here.
------------------------------------------------------------------------

applicantToken : Spacy.SpacyTokenObservation
applicantToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 1) sentenceId 1 137 146 (sym 1001)
    (Spacy.parserLemma (sym 2001)) (ann 3001) (ann 4001) (ann 5001)
    Spacy.nothing (Spacy.declaredHeadAt 147 156)

submittedToken : Spacy.SpacyTokenObservation
submittedToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 2) sentenceId 2 147 156 (sym 1002)
    (Spacy.parserLemma (sym 2002)) (ann 3002) (ann 4002) (ann 5002)
    Spacy.nothing Spacy.declaredSelfHead

grantToken : Spacy.SpacyTokenObservation
grantToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 3) sentenceId 5 166 171 (sym 1003)
    (Spacy.parserLemma (sym 2003)) (ann 3003) (ann 4003) (ann 5003)
    Spacy.nothing (Spacy.declaredHeadAt 221 230)

conferredToken : Spacy.SpacyTokenObservation
conferredToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 4) sentenceId 17 221 230 (sym 1004)
    (Spacy.parserLemma (sym 2004)) (ann 3004) (ann 4004) (ann 5004)
    Spacy.nothing (Spacy.declaredHeadAt 147 156)

rightToken : Spacy.SpacyTokenObservation
rightToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 5) sentenceId 19 233 238 (sym 1005)
    (Spacy.parserLemma (sym 2005)) (ann 3005) (ann 4005) (ann 5005)
    Spacy.nothing (Spacy.declaredHeadAt 221 230)

------------------------------------------------------------------------
-- Existing canonical dependency candidates where the old DependencyShape
-- actually has the correct constructor.
------------------------------------------------------------------------

reportingSourceWitness : Candidate.DependencyWitness
reportingSourceWitness =
  Candidate.dependencyWitness
    applicantToken submittedToken Candidate.nominalSubject
    "receipt sentence 1: nsubj(submitted, applicant), spans 137:146 -> 147:156"

reportingSourceCandidate : Candidate.CandidateSemanticFragment
reportingSourceCandidate =
  Candidate.subjectCandidate reportingSourceWitness "submit-e" "applicant"

embeddedGrantWitness : Candidate.DependencyWitness
embeddedGrantWitness =
  Candidate.dependencyWitness
    grantToken conferredToken Candidate.nominalSubject
    "receipt sentence 1: nsubj(conferred, grant), spans 166:171 -> 221:230"

embeddedGrantCandidate : Candidate.CandidateSemanticFragment
embeddedGrantCandidate =
  Candidate.subjectCandidate embeddedGrantWitness "confer-e" "grant-of-lease"

embeddedRightWitness : Candidate.DependencyWitness
embeddedRightWitness =
  Candidate.dependencyWitness
    rightToken conferredToken Candidate.directObject
    "receipt sentence 1: dobj(conferred, right), spans 233:238 -> 221:230"

embeddedRightCandidate : Candidate.CandidateSemanticFragment
embeddedRightCandidate =
  Candidate.objectCandidate embeddedRightWitness "confer-e" "right"

------------------------------------------------------------------------
-- The receipt's literal ccomp edge.  Do not coerce it into nominalModifier or
-- another older generic dependency constructor merely to fit that enum.
------------------------------------------------------------------------

record EmbeddedPropositionDependencyReceipt : Set where
  constructor embeddedPropositionDependencyReceipt
  field
    reportingPredicate : Spacy.SpacyTokenObservation
    embeddedPredicate : Spacy.SpacyTokenObservation
    rawDependency : String
    reportingSpan : String
    embeddedSpan : String
    sameSentence :
      Spacy.sentence reportingPredicate ≡ Spacy.sentence embeddedPredicate
    embeddedPropositionCandidate : Bool
    embeddedPropositionCandidateIsTrue : embeddedPropositionCandidate ≡ true

open EmbeddedPropositionDependencyReceipt public

embeddedCcomp : EmbeddedPropositionDependencyReceipt
embeddedCcomp =
  embeddedPropositionDependencyReceipt
    submittedToken
    conferredToken
    "ccomp"
    "147:156"
    "221:230"
    refl
    true refl

------------------------------------------------------------------------
-- Reporting composition.  The source candidate and embedded clause are both
-- parser-supported but remain candidate-only.  The source identity is not
-- obtained from string search; the nsubj witness is retained as its evidence.
------------------------------------------------------------------------

embeddedFibre : Candidate.CandidateSemanticFibre
embeddedFibre =
  Candidate.candidateSemanticFibre
    (embeddedGrantCandidate ∷ embeddedRightCandidate ∷ [])
    "PDF-backed embedded proposition fibre: grant as candidate actor; right as candidate patient"

embeddedFormula : Candidate.Formula
embeddedFormula =
  Candidate._∧_
    (Candidate.atom "Confer" (Candidate.eventTerm "confer-e" ∷ []))
    (Candidate._∧_
      (Candidate.formula embeddedGrantCandidate)
      (Candidate.formula embeddedRightCandidate))

record ReportingAttributionCompositionReceipt : Set where
  constructor reportingAttributionCompositionReceipt
  field
    provenance : ReportingFixtureProvenance
    sourceDependency : Candidate.DependencyWitness
    sourceCandidate : Candidate.CandidateSemanticFragment
    sourceCandidateIsCandidateOnly : Candidate.candidateOnly sourceCandidate ≡ true
    embeddedDependency : EmbeddedPropositionDependencyReceipt
    propositionFibre : Candidate.CandidateSemanticFibre
    propositionFormula : Candidate.Formula
    sourceResolutionReference : String
    lexicalDiscoveryUsedOnlyToFindCandidate : Bool
    lexicalDiscoveryUsedOnlyToFindCandidateIsTrue :
      lexicalDiscoveryUsedOnlyToFindCandidate ≡ true
    lexicalDiscoveryIsSemanticAuthority : Bool
    lexicalDiscoveryIsSemanticAuthorityIsFalse :
      lexicalDiscoveryIsSemanticAuthority ≡ false

open ReportingAttributionCompositionReceipt public

reportingComposition : ReportingAttributionCompositionReceipt
reportingComposition =
  reportingAttributionCompositionReceipt
    fixtureProvenance
    reportingSourceWitness
    reportingSourceCandidate
    refl
    embeddedCcomp
    embeddedFibre
    embeddedFormula
    "source candidate backed by literal nsubj(submitted, applicant); no surface-string identity closure"
    true refl
    false refl

------------------------------------------------------------------------
-- Existing parser/PNF -> ITIR compiler now consumes the embedded proposition.
-- The ITIR claim is ABOUT the embedded `confer-e` event and is asserted by the
-- applicant perspective.  The reporting `submit-e` event remains provenance,
-- not the world occurrence asserted by the embedded proposition.
------------------------------------------------------------------------

ontologyInput : Compiler.ParserSemanticOntologyInput
ontologyInput =
  Compiler.parserSemanticOntologyInput
    conferredToken
    (grantToken ∷ rightToken ∷ submittedToken ∷ applicantToken ∷ [])
    embeddedFibre
    embeddedFormula
    (Ontology.stableId "event:pdf-native-title:confer-exclusive-possession:1")
    (Ontology.stableId "event-class:reported-legal-proposition")
    (Ontology.stableId "claim:pdf-native-title:applicant-submission:1")
    (Ontology.stableId "perspective:pdf-native-title:applicant")
    (Ontology.stableId "actor:pdf-native-title:applicant")
    "embedded proposition candidate: grant of Lease conferred a right of exclusive possession"
    "The applicant submitted that the grant of the Lease ... conferred a right of exclusive possession ..."
    "applicant submission perspective"
    "reporting-attribution-fixture-v01 sentence 1 ccomp/nsubj/dobj structure"
    "embedded proposition candidate preserved from materialised PDF-backed spaCy receipt"
    "speaker/source candidate backed by nsubj(submitted, applicant); perspective identity supplied explicitly"
    false refl
    false refl

ontologyOutput : Compiler.ParserSemanticOntologyOutput ontologyInput
ontologyOutput = Compiler.compileParserSemanticOntology ontologyInput

embeddedEvent : Ontology.Event
embeddedEvent = Compiler.event ontologyOutput

applicantPerspective : Ontology.Perspective
applicantPerspective = Compiler.perspective ontologyOutput

applicantClaim : Ontology.Claim
applicantClaim = Compiler.claim ontologyOutput

sameClaimEvent :
  Ontology.Claim.aboutEvent applicantClaim ≡ Ontology.Event.eventId embeddedEvent
sameClaimEvent = refl

sameClaimSpeaker :
  Ontology.Claim.assertedBy applicantClaim
  ≡ Ontology.Perspective.speakerId applicantPerspective
sameClaimSpeaker = refl

------------------------------------------------------------------------
-- Status refinement.  Parser construction begins mentioned-only.  The
-- reporting/source receipt licenses asserted-by-source / asserted-occurrence
-- status, but not occurrence admission or truth admission.
------------------------------------------------------------------------

sourceProposition : Status.PropositionStatusProduct
sourceProposition =
  Status.propositionStatusProduct
    (Ontology.StableId.value (Ontology.Claim.claimId applicantClaim))
    Status.assertedBySource
    Status.truthUnresolved
    Status.propositionSource
    Status.evidenceNeutral
    Status.sourceEvidence
    Status.modalityKindUnresolved
    Status.modalForceUnresolved
    Status.scopeUnresolved

sourceEventStatus : Status.EventStatusProduct
sourceEventStatus =
  Status.eventStatusProduct
    (Ontology.StableId.value (Ontology.Event.eventId embeddedEvent))
    Status.assertedOccurrence
    Status.eventTime
    Status.scopeUnresolved

propositionReceipt : Status.PropositionResolutionReceipt
propositionReceipt =
  Status.propositionResolutionReceipt
    sourceProposition
    Status.assertedBySource
    Status.truthUnresolved
    "nsubj(submitted, applicant) + ccomp(submitted, conferred) reporting composition"
    ("PDF paragraph sha256:84eeb6e3b6900521796fd1d669b7f8b1998d652ce8fed0a98fc0486b01e2a01d" ∷ [])
    "reporting-attribution parser/status fixture; candidate-only"

occurrenceReceipt : Status.OccurrenceResolutionReceipt
occurrenceReceipt =
  Status.occurrenceResolutionReceipt
    sourceEventStatus
    Status.assertedOccurrence
    ("claim:pdf-native-title:applicant-submission:1" ∷ [])
    ("materialised ccomp/nsubj/dobj parser evidence" ∷ [])
    "asserted occurrence means asserted by source; no occurrence-admission authority"

reportingLegalGate : Legal.SemanticLegalInputGate embeddedEvent
reportingLegalGate =
  Legal.semanticLegalInputGate
    sourceEventStatus
    sourceProposition
    refl
    Status.applicabilityCandidate
    Legal.assertionCandidateUse

reportingTruthStillUnresolved :
  Status.resultingTruthStatus propositionReceipt ≡ Status.truthUnresolved
reportingTruthStillUnresolved = refl

reportingOccurrenceIsAssertedNotAdmitted :
  Status.resultingOccurrenceStatus occurrenceReceipt ≡ Status.assertedOccurrence
reportingOccurrenceIsAssertedNotAdmitted = refl

reportingLegalUseIsCandidateOnly :
  Legal.SemanticLegalInputGate.resultingApplicability reportingLegalGate
  ≡ Status.applicabilityCandidate
reportingLegalUseIsCandidateOnly = refl

------------------------------------------------------------------------
-- Hard non-promotion boundaries surfaced by the PDF-backed fixture.
------------------------------------------------------------------------

data ReportingLemmaChoosesSemanticStatus : Set where
data SurfaceSourceSearchProvesAttribution : Set where
data CcompEdgeProvesEmbeddedTruth : Set where
data ApplicantSubmissionProvesOccurrence : Set where
data ApplicantSubmissionAuthorizesLegalApplicability : Set where

reportingLemmaDoesNotChooseSemanticStatus :
  ReportingLemmaChoosesSemanticStatus → ⊥
reportingLemmaDoesNotChooseSemanticStatus ()

surfaceSearchDoesNotProveAttribution :
  SurfaceSourceSearchProvesAttribution → ⊥
surfaceSearchDoesNotProveAttribution ()

ccompDoesNotProveEmbeddedTruth : CcompEdgeProvesEmbeddedTruth → ⊥
ccompDoesNotProveEmbeddedTruth ()

submissionDoesNotProveOccurrence : ApplicantSubmissionProvesOccurrence → ⊥
submissionDoesNotProveOccurrence ()

submissionDoesNotAuthorizeAdmittedApplicability :
  ApplicantSubmissionAuthorizesLegalApplicability → ⊥
submissionDoesNotAuthorizeAdmittedApplicability ()
