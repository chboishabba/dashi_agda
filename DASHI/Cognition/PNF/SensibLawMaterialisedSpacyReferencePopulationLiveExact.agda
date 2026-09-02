module DASHI.Cognition.PNF.SensibLawMaterialisedSpacyReferencePopulationLiveExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionExact as Constitution
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawAntecedentIdentityRefinementBidiExact as Identity
import DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact as Trace

------------------------------------------------------------------------
-- MATERIALISED SPACY -> REFERENCE POPULATION
--
-- Reuses the real en_core_web_sm parse already transcribed in
-- SpacyNegatedCoordinationScopeTraceExact.  In particular the source sentence
-- contains both the initial mention `It` and the later reflexive occurrence
-- `itself`.  This owner uses those literal parser observations to populate the
-- existing antecedent/reference fibre.  It does NOT infer coreference merely
-- from token text, same-sentence position, or the reflexive-looking surface.
------------------------------------------------------------------------

record ParserMentionCandidate : Set where
  constructor parserMentionCandidate
  field
    mentionObservation : Spacy.SpacyTokenObservation
    candidateObservation : Spacy.SpacyTokenObservation
    accessibilityPath : Constitution.AccessibilityPath
    sameSentenceEvidence :
      Spacy.sentence mentionObservation ≡ Spacy.sentence candidateObservation
    candidateReference : String
    evidenceReference : String

open ParserMentionCandidate public

record MaterialisedReferencePopulationReceipt : Set where
  constructor materialisedReferencePopulationReceipt
  field
    sourceSentence : String
    mention : Spacy.SpacyTokenObservation
    candidate : Spacy.SpacyTokenObservation
    parserCandidate : ParserMentionCandidate
    semanticSubject : Status.SemanticSubject
    bindingSnapshot : Identity.BindingCandidateSnapshot
    antecedentReceipt : Status.AntecedentResolutionReceipt
    parserObservationRetained : Bool
    candidateOnly : Bool
    identityClosed : Bool

open MaterialisedReferencePopulationReceipt public

------------------------------------------------------------------------
-- Canonical live reference fixture: `itself` receives `It` as one structurally
-- accessible candidate from the same materialised parser sentence.  This is a
-- candidate-population result only; no identity/coreference closure is claimed.
------------------------------------------------------------------------

itselfToItCandidate : ParserMentionCandidate
itselfToItCandidate =
  parserMentionCandidate
    Trace.itselfToken
    Trace.itToken
    Constitution.sameSentence
    refl
    "materialised-spacy:sentence-1/token-1"
    "same materialised spaCy sentence; candidate accessibility only"

itselfSubject : Status.SemanticSubject
itselfSubject =
  Status.semanticSubject
    "materialised-spacy:sentence-1/token-15"
    Status.entityReferent
    Status.participantUnresolved
    Status.legalParticipantUnresolved
    Status.identityUnresolved
    Status.antecedentCandidateSet

itselfCandidateSnapshot : Identity.BindingCandidateSnapshot
itselfCandidateSnapshot =
  Identity.bindingCandidateSnapshot
    "materialised-spacy:sentence-1/token-15:antecedent-candidates"
    ("materialised-spacy:sentence-1/token-1" ∷ [])
    (Constitution.sameSentence ∷ [])
    ("actual en_core_web_sm token observations retained" ∷
     "same-sentence structural accessibility only" ∷ [])

itselfAntecedentReceipt : Status.AntecedentResolutionReceipt
itselfAntecedentReceipt =
  Status.antecedentResolutionReceipt
    itselfSubject
    Status.antecedentCandidateSet
    ("sameSentence(materialised token 15, token 1)" ∷ [])
    "materialised-spacy:sentence-1/token-15:antecedent-candidates"
    "reference-population-only:no-identity-closure"

canonicalMaterialisedReferencePopulation : MaterialisedReferencePopulationReceipt
canonicalMaterialisedReferencePopulation =
  materialisedReferencePopulationReceipt
    Trace.sourceSentence
    Trace.itselfToken
    Trace.itToken
    itselfToItCandidate
    itselfSubject
    itselfCandidateSnapshot
    itselfAntecedentReceipt
    true
    true
    false

sameLiteralParserSentence :
  Spacy.sentence
    (mention canonicalMaterialisedReferencePopulation)
  ≡ Spacy.sentence
    (candidate canonicalMaterialisedReferencePopulation)
sameLiteralParserSentence = refl

candidatePopulationLeavesIdentityUnresolved :
  Status.identityStatus
    (semanticSubject canonicalMaterialisedReferencePopulation)
  ≡ Status.identityUnresolved
candidatePopulationLeavesIdentityUnresolved = refl

candidatePopulationRecordsAntecedentFibre :
  Status.antecedentStatus
    (semanticSubject canonicalMaterialisedReferencePopulation)
  ≡ Status.antecedentCandidateSet
candidatePopulationRecordsAntecedentFibre = refl

------------------------------------------------------------------------
-- Boundaries.  The actual parse supplies mention coordinates and structural
-- accessibility, but not a proof that the two mentions have identical referent.
------------------------------------------------------------------------

data SameSentenceProvesCoreference : Set where
data ReflexiveSurfaceProvesIdentity : Set where
data ParserMentionCandidateAuthorizesIdentityClosure : Set where

data MaterialisedFixtureMeansGeneralReferenceCompiler : Set where

sameSentenceDoesNotProveCoreference : SameSentenceProvesCoreference → ⊥
sameSentenceDoesNotProveCoreference ()

reflexiveSurfaceDoesNotProveIdentity : ReflexiveSurfaceProvesIdentity → ⊥
reflexiveSurfaceDoesNotProveIdentity ()

parserCandidateDoesNotAuthorizeIdentityClosure :
  ParserMentionCandidateAuthorizesIdentityClosure → ⊥
parserCandidateDoesNotAuthorizeIdentityClosure ()

fixtureDoesNotMeanGeneralCompiler :
  MaterialisedFixtureMeansGeneralReferenceCompiler → ⊥
fixtureDoesNotMeanGeneralCompiler ()
