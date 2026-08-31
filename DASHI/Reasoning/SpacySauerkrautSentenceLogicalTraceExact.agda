module DASHI.Reasoning.SpacySauerkrautSentenceLogicalTraceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.NumericAuthority as Authority
import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.SpacyExecutableSemanticRuleBankExact as Rules

------------------------------------------------------------------------
-- EXACT SENTENCE SPECIMEN
--
-- This is a finite expected-dependency specimen for the sentence below. It is
-- not represented as an already-materialised SensibLaw parser run. The purpose
-- is to make the dependency -> candidate semantics -> logical formula path
-- inspectable while retaining parser/semantic non-identity.
------------------------------------------------------------------------

sourceSentence : String
sourceSentence = "Raw sauerkraut juice reduced glyphosate residues."

sentenceId : Authority.SentenceId
sentenceId = Authority.sentenceId 1

ann : Nat → Spacy.NumericAnnotation
ann n = Spacy.annotationPresent (Authority.symbolId n)

rawToken : Spacy.SpacyTokenObservation
rawToken = Spacy.spacyTokenObservation
  (Authority.tokenId 1) sentenceId 0 0 3 (Authority.symbolId 101)
  (Spacy.parserLemma (Authority.symbolId 201))
  (ann 301) (ann 401) (ann 501) Spacy.nothing
  (Spacy.declaredHeadAt 15 20)

sauerkrautToken : Spacy.SpacyTokenObservation
sauerkrautToken = Spacy.spacyTokenObservation
  (Authority.tokenId 2) sentenceId 1 4 14 (Authority.symbolId 102)
  (Spacy.parserLemma (Authority.symbolId 202))
  (ann 302) (ann 402) (ann 502) Spacy.nothing
  (Spacy.declaredHeadAt 15 20)

juiceToken : Spacy.SpacyTokenObservation
juiceToken = Spacy.spacyTokenObservation
  (Authority.tokenId 3) sentenceId 2 15 20 (Authority.symbolId 103)
  (Spacy.parserLemma (Authority.symbolId 203))
  (ann 303) (ann 403) (ann 503) Spacy.nothing
  (Spacy.declaredHeadAt 21 28)

reducedToken : Spacy.SpacyTokenObservation
reducedToken = Spacy.spacyTokenObservation
  (Authority.tokenId 4) sentenceId 3 21 28 (Authority.symbolId 104)
  (Spacy.parserLemma (Authority.symbolId 204))
  (ann 304) (ann 404) (ann 504) Spacy.nothing
  Spacy.declaredSelfHead

glyphosateToken : Spacy.SpacyTokenObservation
glyphosateToken = Spacy.spacyTokenObservation
  (Authority.tokenId 5) sentenceId 4 29 39 (Authority.symbolId 105)
  (Spacy.parserLemma (Authority.symbolId 205))
  (ann 305) (ann 405) (ann 505) Spacy.nothing
  (Spacy.declaredHeadAt 40 48)

residuesToken : Spacy.SpacyTokenObservation
residuesToken = Spacy.spacyTokenObservation
  (Authority.tokenId 6) sentenceId 5 40 48 (Authority.symbolId 106)
  (Spacy.parserLemma (Authority.symbolId 206))
  (ann 306) (ann 406) (ann 506) Spacy.nothing
  (Spacy.declaredHeadAt 21 28)

------------------------------------------------------------------------
-- Expected structural dependency witnesses relevant to event semantics.
-- Compound/adjectival lexical composition is retained as an entity-resolution
-- residual rather than silently deriving rawSauerkrautJuice/glyphosateResidues
-- from spaCy alone in this specimen.
------------------------------------------------------------------------

subjectWitness : Candidate.DependencyWitness
subjectWitness = Candidate.dependencyWitness
  juiceToken reducedToken Candidate.nominalSubject
  "expected spaCy shape: nsubj(reduced, juice)"

objectWitness : Candidate.DependencyWitness
objectWitness = Candidate.dependencyWitness
  residuesToken reducedToken Candidate.directObject
  "expected spaCy shape: obj(reduced, residues)"

subjectShapeAdmission : Rules.ShapeAdmission subjectWitness Candidate.nominalSubject
subjectShapeAdmission = Rules.shapeAdmission refl
  "semantic-rule-bank:nsubj->Actor:v1"
  "spaCy dependency label nsubj"

objectShapeAdmission : Rules.ShapeAdmission objectWitness Candidate.directObject
objectShapeAdmission = Rules.shapeAdmission refl
  "semantic-rule-bank:obj->Patient:v1"
  "spaCy dependency label obj"

subjectCandidate : Candidate.CandidateSemanticFragment
subjectCandidate = Rules.nsubjActorRule
  subjectWitness subjectShapeAdmission "reduce-e" "rawSauerkrautJuice"

objectCandidate : Candidate.CandidateSemanticFragment
objectCandidate = Rules.objPatientRule
  objectWitness objectShapeAdmission "reduce-e" "glyphosateResidues"

reduceEvent : Candidate.Formula
reduceEvent = Candidate.atom "Reduce" (Candidate.eventTerm "reduce-e" ∷ [])

actorFormula : Candidate.Formula
actorFormula = Candidate.formula subjectCandidate

patientFormula : Candidate.Formula
patientFormula = Candidate.formula objectCandidate

sentenceLogicalCandidate : Candidate.Formula
sentenceLogicalCandidate =
  Candidate.existsF "e" "Event"
    (Candidate._∧_
      reduceEvent
      (Candidate._∧_ actorFormula patientFormula))

expectedDavidsonianReading : Candidate.Formula
expectedDavidsonianReading =
  Candidate.existsF "e" "Event"
    (Candidate._∧_
      (Candidate.atom "Reduce" (Candidate.eventTerm "reduce-e" ∷ []))
      (Candidate._∧_
        (Candidate.atom "Actor"
          (Candidate.eventTerm "reduce-e" ∷ Candidate.entityTerm "rawSauerkrautJuice" ∷ []))
        (Candidate.atom "Patient"
          (Candidate.eventTerm "reduce-e" ∷ Candidate.entityTerm "glyphosateResidues" ∷ []))))

sentenceLogicalCandidateHasExpectedShape :
  sentenceLogicalCandidate ≡ expectedDavidsonianReading
sentenceLogicalCandidateHasExpectedShape = refl

semanticFibre : Candidate.CandidateSemanticFibre
semanticFibre = Candidate.candidateSemanticFibre
  (subjectCandidate ∷ objectCandidate ∷ [])
  "two role candidates licensed by expected nsubj/obj observations; lexical compound/entity readings remain separate residuals"

------------------------------------------------------------------------
-- The important evidential ambiguity: lexical verb semantics do not decide
-- whether 'reduced' reports a descriptive temporal decline, an association, or
-- an identified causal treatment effect. That judgment belongs downstream.
------------------------------------------------------------------------

data ReducedInferentialReading : Set where
  descriptiveReductionReading
  associationalReductionReading
  causalReductionReading
  : ReducedInferentialReading

record ReducedReadingFibre : Set where
  constructor reducedReadingFibre
  field
    readings : List ReducedInferentialReading
    lexicalSemanticsReference : String
    experimentalDesignResolutionReference : String

canonicalReducedReadingFibre : ReducedReadingFibre
canonicalReducedReadingFibre = reducedReadingFibre
  ( descriptiveReductionReading
  ∷ associationalReductionReading
  ∷ causalReductionReading
  ∷ [])
  "surface predicate 'reduced' alone does not identify evidential force"
  "experimental design, comparator, timing and causal-identification receipts decide admissible inferential force"

record SentenceTraceBoundary : Set where
  constructor sentenceTraceBoundary
  field
    specimenIsClaimedMaterialisedSpacyRun : Bool
    specimenIsClaimedMaterialisedSpacyRunIsFalse :
      specimenIsClaimedMaterialisedSpacyRun ≡ false
    nsubjAndObjCanProduceCandidateEventRoles : Bool
    nsubjAndObjCanProduceCandidateEventRolesIsTrue :
      nsubjAndObjCanProduceCandidateEventRoles ≡ true
    exactDavidsonianCandidateShapeIsExhibited : Bool
    exactDavidsonianCandidateShapeIsExhibitedIsTrue :
      exactDavidsonianCandidateShapeIsExhibited ≡ true
    lexicalReducedImpliesCausalForce : Bool
    lexicalReducedImpliesCausalForceIsFalse :
      lexicalReducedImpliesCausalForce ≡ false
    entityCompoundResolutionStillHasResidual : Bool
    entityCompoundResolutionStillHasResidualIsTrue :
      entityCompoundResolutionStillHasResidual ≡ true

canonicalSentenceTraceBoundary : SentenceTraceBoundary
canonicalSentenceTraceBoundary =
  sentenceTraceBoundary false refl true refl true refl false refl true refl
