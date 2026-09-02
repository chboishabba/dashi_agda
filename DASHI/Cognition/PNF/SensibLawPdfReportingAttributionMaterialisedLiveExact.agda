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
import DASHI.Reasoning.SpacyExecutableSemanticRuleBankExact as RuleBank
import DASHI.Cognition.PNF.SensibLawMaterialisedSpacyToOntologyVerticalExact as Compiler
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact as Consumer
import DASHI.Interop.SensibLawOntologyTopology as Ontology

------------------------------------------------------------------------
-- PDF-BACKED MATERIALISED GENERAL-DISCOURSE ATTRIBUTION VERTICAL
--
-- Source receipt: sensiblaw.reporting-attribution-fixture.v0_1
-- text sha256: 84eeb6e3b6900521796fd1d669b7f8b1998d652ce8fed0a98fc0486b01e2a01d
--
-- This owner is domain-neutral through parser, clause and discourse structure.
-- The same carrier may later receive a legal submission projection, but nothing
-- here requires that legal consumer.
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
    false refl false refl true refl false refl

sentenceId : Authority.SentenceId
sentenceId = Authority.sentenceId 1

sym : Nat → Authority.SymbolId
sym = Authority.symbolId

ann : Nat → Spacy.NumericAnnotation
ann n = Spacy.annotationPresent (sym n)

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

reportingSourceWitness : Candidate.DependencyWitness
reportingSourceWitness =
  Candidate.dependencyWitness
    applicantToken submittedToken Candidate.nominalSubject
    "receipt sentence 1: nsubj(submitted, applicant), spans 137:146 -> 147:156"

reportingSourceAdmission :
  RuleBank.ShapeAdmission reportingSourceWitness Candidate.nominalSubject
reportingSourceAdmission =
  RuleBank.shapeAdmission refl
    "rulebank-v0.2 general discourse subject admission"
    "spaCy nsubj"

reportingSourceCandidate : Candidate.CandidateSemanticFragment
reportingSourceCandidate =
  RuleBank.nsubjActorRule reportingSourceWitness reportingSourceAdmission
    "submit-e" "applicant"

embeddedCcompWitness : Candidate.DependencyWitness
embeddedCcompWitness =
  Candidate.dependencyWitness
    conferredToken submittedToken Candidate.clausalComplement
    "receipt sentence 1: ccomp(submitted, conferred), spans 221:230 -> 147:156"

embeddedCcompAdmission :
  RuleBank.ShapeAdmission embeddedCcompWitness Candidate.clausalComplement
embeddedCcompAdmission =
  RuleBank.shapeAdmission refl
    "rulebank-v0.2 general clausal complement admission"
    "spaCy ccomp"

embeddedContentCandidate : Candidate.CandidateSemanticFragment
embeddedContentCandidate =
  RuleBank.clausalComplementRule embeddedCcompWitness embeddedCcompAdmission
    "submit-e" "confer-e"

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

embeddedFibre : Candidate.CandidateSemanticFibre
embeddedFibre =
  Candidate.candidateSemanticFibre
    (embeddedContentCandidate ∷ embeddedGrantCandidate ∷ embeddedRightCandidate ∷ [])
    "PDF-backed general content-clause fibre; no legal classification required"

embeddedFormula : Candidate.Formula
embeddedFormula =
  Candidate._∧_
    (Candidate.formula embeddedContentCandidate)
    (Candidate._∧_
      (Candidate.formula embeddedGrantCandidate)
      (Candidate.formula embeddedRightCandidate))

record ReportingAttributionCompositionReceipt : Set where
  constructor reportingAttributionCompositionReceipt
  field
    provenance : ReportingFixtureProvenance
    sourceDependency : Candidate.DependencyWitness
    sourceCandidate : Candidate.CandidateSemanticFragment
    contentDependency : Candidate.DependencyWitness
    contentCandidate : Candidate.CandidateSemanticFragment
    propositionFibre : Candidate.CandidateSemanticFibre
    propositionFormula : Candidate.Formula
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
    reportingSourceWitness reportingSourceCandidate
    embeddedCcompWitness embeddedContentCandidate
    embeddedFibre embeddedFormula
    true refl false refl

------------------------------------------------------------------------
-- Domain-neutral discourse candidate.  This is usable by ordinary text
-- consumers without selecting any legal ontology or judicial status.
------------------------------------------------------------------------

discourseCandidate : Consumer.DiscourseActCandidate
discourseCandidate =
  Consumer.discourseActCandidate
    reportingSourceCandidate
    reportingSourceCandidate
    embeddedContentCandidate
    "actor:pdf-native-title:applicant"
    "event:pdf-native-title:confer-exclusive-possession:1"
    ( "nsubj(submitted, applicant)"
    ∷ "ccomp(submitted, conferred)"
    ∷ "paragraph sha256:84eeb6e3b6900521796fd1d669b7f8b1998d652ce8fed0a98fc0486b01e2a01d"
    ∷ [])
    true refl

generalDiscourseResolution : Consumer.GeneralDiscourseResolution discourseCandidate
generalDiscourseResolution =
  Consumer.generalDiscourseResolution
    Consumer.reportDiscourse
    Status.assertedBySource
    Status.assertedOccurrence
    Status.truthUnresolved
    Status.propositionSource
    "source/content structure supports attributed report/assertion; legal role intentionally absent"
    false refl

generalConsumerInterpretation :
  Consumer.ConsumerIndexedDiscourseInterpretation
    discourseCandidate generalDiscourseResolution
generalConsumerInterpretation =
  Consumer.generalOnlyInterpretation generalDiscourseResolution

------------------------------------------------------------------------
-- Generic parser/PNF -> ITIR carrier.  IDs remain domain-neutral; later legal
-- consumers may project this same carrier into a case/submission context.
------------------------------------------------------------------------

ontologyInput : Compiler.ParserSemanticOntologyInput
ontologyInput =
  Compiler.parserSemanticOntologyInput
    conferredToken
    (grantToken ∷ rightToken ∷ submittedToken ∷ applicantToken ∷ [])
    embeddedFibre
    embeddedFormula
    (Ontology.stableId "event:pdf-native-title:confer-exclusive-possession:1")
    (Ontology.stableId "event-class:proposition-content")
    (Ontology.stableId "claim:pdf-native-title:reported-content:1")
    (Ontology.stableId "perspective:pdf-native-title:applicant")
    (Ontology.stableId "actor:pdf-native-title:applicant")
    "content proposition candidate: grant of Lease conferred a right of exclusive possession"
    "The applicant submitted that the grant of the Lease ... conferred a right of exclusive possession ..."
    "source-attributed discourse perspective"
    "reporting-attribution-fixture-v01 generic nsubj+ccomp content structure"
    "content-clause candidate preserved from materialised PDF-backed spaCy receipt"
    "speaker/source candidate backed by nsubj(submitted, applicant); identity supplied explicitly"
    false refl false refl

ontologyOutput : Compiler.ParserSemanticOntologyOutput ontologyInput
ontologyOutput = Compiler.compileParserSemanticOntology ontologyInput

embeddedEvent : Ontology.Event
embeddedEvent = Compiler.event ontologyOutput

applicantPerspective : Ontology.Perspective
applicantPerspective = Compiler.perspective ontologyOutput

applicantClaim : Ontology.Claim
applicantClaim = Compiler.claim ontologyOutput

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
    sourceProposition Status.assertedBySource Status.truthUnresolved
    "generic nsubj + clausalComplement discourse composition"
    ("PDF paragraph sha256:84eeb6e3b6900521796fd1d669b7f8b1998d652ce8fed0a98fc0486b01e2a01d" ∷ [])
    "general discourse resolution; no legal consumer required"

occurrenceReceipt : Status.OccurrenceResolutionReceipt
occurrenceReceipt =
  Status.occurrenceResolutionReceipt
    sourceEventStatus Status.assertedOccurrence
    ("claim:pdf-native-title:reported-content:1" ∷ [])
    ("materialised nsubj+ccomp+nsubj+dobj parser evidence" ∷ [])
    "asserted occurrence means asserted by source; no occurrence-admission authority"

reportingLegalGate : Legal.SemanticLegalInputGate embeddedEvent
reportingLegalGate =
  Legal.semanticLegalInputGate
    sourceEventStatus sourceProposition refl
    Status.applicabilityCandidate Legal.assertionCandidateUse

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
-- Hard boundaries.
------------------------------------------------------------------------

data ReportingLemmaChoosesSemanticStatus : Set where
data SurfaceSourceSearchProvesAttribution : Set where
data CcompEdgeProvesEmbeddedTruth : Set where
data GeneralDiscourseAutomaticallyLegal : Set where
data ApplicantSubmissionProvesOccurrence : Set where

reportingLemmaDoesNotChooseSemanticStatus :
  ReportingLemmaChoosesSemanticStatus → ⊥
reportingLemmaDoesNotChooseSemanticStatus ()

surfaceSearchDoesNotProveAttribution :
  SurfaceSourceSearchProvesAttribution → ⊥
surfaceSearchDoesNotProveAttribution ()

ccompDoesNotProveEmbeddedTruth : CcompEdgeProvesEmbeddedTruth → ⊥
ccompDoesNotProveEmbeddedTruth ()

generalDiscourseDoesNotAutomaticallyBecomeLegal :
  GeneralDiscourseAutomaticallyLegal → ⊥
generalDiscourseDoesNotAutomaticallyBecomeLegal ()

submissionDoesNotProveOccurrence : ApplicantSubmissionProvesOccurrence → ⊥
submissionDoesNotProveOccurrence ()
