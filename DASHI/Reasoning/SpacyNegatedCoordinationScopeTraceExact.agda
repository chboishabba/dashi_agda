module DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.NumericAuthority as Authority
import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.SpacyExecutableSemanticRuleBankExact as RuleBank
import DASHI.Reasoning.SpacyPNF369DialecticBridgeExact as Bridge369
import DASHI.Reasoning.SpacyPNF369LogicalQualificationExact as Capstone
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as Evidence
import DASHI.Reasoning.PredicateNormalFormLogicalCalculusExact as Logic

open Candidate using (Formula; Term; atom; _∧_; _∨_; _⇒_; notF)
open Logic using (_⊢_; assumption; here; there)
open Bridge369 using (rejectCandidate; suspendCandidate; admitCandidate)

-----------------------------------------------------------------------
-- MATERIALISED SPACY SPECIMEN
--
-- A real spaCy parse (en_core_web_sm) of the SensibLaw README sentence
--
--     "It does not mutate live StatiBaker state, mark work complete,
--      or promote tasks by itself."
--
-- The flat dependency graph is retained as numeric parser evidence.  The
-- negation 'neg' edge heads the ROOT verb 'mutate', while the coordination
-- 'or' joins 'promote' back into the same verb group.  Whether 'neg' takes
-- narrow scope over just 'mutate' or broad de Morgan scope over the whole
-- coordination is NOT decided by the flat dependency parse: it remains a
-- scope-review decision downstream.  This module builds the complete
--
--     dependency graph -> {phi_A, phi_B} -> (+,0,-) review path
--       -> reviewed PNF -> Gamma |- psi
--
-- and records that two different parser/semantic/dialectical histories can
-- reconverge on the SAME final logical formula without collapsing into one
-- history.
-----------------------------------------------------------------------

sourceSentence : String
sourceSentence =
  "It does not mutate live StatiBaker state , mark work complete , "
    ++ "or promote tasks by itself ."

sentenceId : Authority.SentenceId
sentenceId = Authority.sentenceId 1

sym : Nat → Authority.SymbolId
sym = Authority.symbolId

ann : Nat → Spacy.NumericAnnotation
ann n = Spacy.annotationPresent (Authority.symbolId n)

-- Numeric token observations transcribed from the actual parse.  Each carries
-- token id, sentence id, local ordinal, char offsets, orth symbol, lemma,
-- pos/tag/dependency symbol ids, no morphology, and the declared head.

itToken : Spacy.SpacyTokenObservation
itToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 1) sentenceId 0 0 2 (sym 1)
    (Spacy.parserLemma (sym 2)) (ann 3) (ann 4) (ann 5) Spacy.nothing
    (Spacy.declaredHeadAt 3 9)

doesToken : Spacy.SpacyTokenObservation
doesToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 2) sentenceId 1 3 7 (sym 6)
    (Spacy.parserLemma (sym 7)) (ann 8) (ann 9) (ann 10) Spacy.nothing
    (Spacy.declaredHeadAt 3 9)

notToken : Spacy.SpacyTokenObservation
notToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 3) sentenceId 2 8 11 (sym 11)
    (Spacy.parserLemma (sym 12)) (ann 13) (ann 14) (ann 15) Spacy.nothing
    (Spacy.declaredHeadAt 3 9)

mutateToken : Spacy.SpacyTokenObservation
mutateToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 4) sentenceId 3 12 18 (sym 16)
    (Spacy.parserLemma (sym 17)) (ann 18) (ann 19) (ann 20) Spacy.nothing
    Spacy.declaredSelfHead

liveToken : Spacy.SpacyTokenObservation
liveToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 5) sentenceId 4 19 23 (sym 21)
    (Spacy.parserLemma (sym 22)) (ann 23) (ann 24) (ann 25) Spacy.nothing
    (Spacy.declaredHeadAt 13 18)

statiBakerToken : Spacy.SpacyTokenObservation
statiBakerToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 6) sentenceId 5 24 34 (sym 26)
    (Spacy.parserLemma (sym 27)) (ann 28) (ann 29) (ann 30) Spacy.nothing
    (Spacy.declaredHeadAt 13 18)

stateToken : Spacy.SpacyTokenObservation
stateToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 7) sentenceId 6 35 40 (sym 31)
    (Spacy.parserLemma (sym 32)) (ann 33) (ann 34) (ann 35) Spacy.nothing
    (Spacy.declaredHeadAt 3 9)

markToken : Spacy.SpacyTokenObservation
markToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 8) sentenceId 7 42 46 (sym 36)
    (Spacy.parserLemma (sym 37)) (ann 38) (ann 39) (ann 40) Spacy.nothing
    (Spacy.declaredHeadAt 7 9)

workToken : Spacy.SpacyTokenObservation
workToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 9) sentenceId 8 47 51 (sym 41)
    (Spacy.parserLemma (sym 42)) (ann 43) (ann 44) (ann 45) Spacy.nothing
    (Spacy.declaredHeadAt 35 40)

completeToken : Spacy.SpacyTokenObservation
completeToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 10) sentenceId 9 52 60 (sym 46)
    (Spacy.parserLemma (sym 47)) (ann 48) (ann 49) (ann 50) Spacy.nothing
    (Spacy.declaredHeadAt 47 51)

orToken : Spacy.SpacyTokenObservation
orToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 11) sentenceId 10 62 64 (sym 51)
    (Spacy.parserLemma (sym 52)) (ann 53) (ann 54) (ann 55) Spacy.nothing
    (Spacy.declaredHeadAt 41 45)

promoteToken : Spacy.SpacyTokenObservation
promoteToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 12) sentenceId 11 65 72 (sym 56)
    (Spacy.parserLemma (sym 57)) (ann 58) (ann 59) (ann 60) Spacy.nothing
    (Spacy.declaredHeadAt 52 60)

tasksToken : Spacy.SpacyTokenObservation
tasksToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 13) sentenceId 12 73 78 (sym 61)
    (Spacy.parserLemma (sym 62)) (ann 63) (ann 64) (ann 65) Spacy.nothing
    (Spacy.declaredHeadAt 65 72)

byToken : Spacy.SpacyTokenObservation
byToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 14) sentenceId 13 79 81 (sym 66)
    (Spacy.parserLemma (sym 67)) (ann 68) (ann 69) (ann 70) Spacy.nothing
    (Spacy.declaredHeadAt 65 72)

itselfToken : Spacy.SpacyTokenObservation
itselfToken =
  Spacy.spacyTokenObservation
    (Authority.tokenId 15) sentenceId 14 82 88 (sym 71)
    (Spacy.parserLemma (sym 72)) (ann 73) (ann 74) (ann 75) Spacy.nothing
    (Spacy.declaredHeadAt 79 81)

-----------------------------------------------------------------------
-- Dependency witnesses retained from the flat parse.
--
-- neg(mutate, not)          -> negation scope candidate
-- cc/conj(mutate, promote)  -> coordination scope candidate
-- dobj(mutate, state)       -> patient role candidate
-- dobj(promote, tasks)      -> patient role candidate
--
-- The two competing SCOPE readings (broad de Morgan vs narrow) both reuse the
-- same two witnesses; the dependency parse does not choose between them.
-----------------------------------------------------------------------

negWitness : Candidate.DependencyWitness
negWitness =
  Candidate.dependencyWitness
    notToken mutateToken Candidate.negation
    "spaCy neg edge: neg(mutate, not) resolved to head 'mutate'"

negAdmission : RuleBank.ShapeAdmission negWitness Candidate.negation
negAdmission =
  RuleBank.shapeAdmission refl
    "semantic-rule-bank:neg->notF:v1"
    "spaCy dependency label neg"

orWitness : Candidate.DependencyWitness
orWitness =
  Candidate.dependencyWitness
    promoteToken mutateToken Candidate.conjunction
    "spaCy cc/conj edge: promote coordinated back to ROOT 'mutate'"

orAdmission : RuleBank.ShapeAdmission orWitness Candidate.conjunction
orAdmission =
  RuleBank.shapeAdmission refl
    "semantic-rule-bank:cc->conjunction:v1"
    "spaCy coordination constructors cc/or + conj/promote"

stateWitness : Candidate.DependencyWitness
stateWitness =
  Candidate.dependencyWitness
    stateToken mutateToken Candidate.directObject
    "spaCy dobj edge: state is direct object of 'mutate'"

stateAdmission : RuleBank.ShapeAdmission stateWitness Candidate.directObject
stateAdmission =
  RuleBank.shapeAdmission refl
    "semantic-rule-bank:obj->Patient:v1"
    "spaCy dependency label dobj"

tasksWitness : Candidate.DependencyWitness
tasksWitness =
  Candidate.dependencyWitness
    tasksToken promoteToken Candidate.directObject
    "spaCy dobj edge: tasks is direct object of 'promote'"

tasksAdmission : RuleBank.ShapeAdmission tasksWitness Candidate.directObject
tasksAdmission =
  RuleBank.shapeAdmission refl
    "semantic-rule-bank:obj->Patient:v1"
    "spaCy dependency label dobj"

-----------------------------------------------------------------------
-- Local surface atoms for the two role predicates.
-----------------------------------------------------------------------

mutateSurface : Formula
mutateSurface =
  atom "Mutate" (Candidate.entityTerm "liveStatiBakerState" ∷ [])

promoteSurface : Formula
promoteSurface =
  atom "Promote" (Candidate.entityTerm "tasks" ∷ [])

coordinationSurface : Formula
coordinationSurface = mutateSurface ∨ promoteSurface

-----------------------------------------------------------------------
-- Candidate semantic fragments.
--
-- Both compete for the same 'neg' edge over different bodies: the parser
-- licenses a 'notF' candidate but does not fix which body the negation
-- scopes.  Both candidates carry the same DependencyWitness; scope is the
-- remaining review decision.
-----------------------------------------------------------------------

negBroadCandidate : Candidate.CandidateSemanticFragment
negBroadCandidate =
  RuleBank.negationScopeRule negWitness negAdmission coordinationSurface

negNarrowCandidate : Candidate.CandidateSemanticFragment
negNarrowCandidate =
  RuleBank.negationScopeRule negWitness negAdmission mutateSurface

-----------------------------------------------------------------------
-- The two competing scope readings.
-----------------------------------------------------------------------

broadBody : Formula
broadBody = notF (mutateSurface ∨ promoteSurface)

narrowBody : Formula
narrowBody = notF mutateSurface

data ScopeReading : Set where
  broadDeMorganReading
  narrowReading
  : ScopeReading

readingFormula : ScopeReading → Formula
readingFormula broadDeMorganReading = broadBody
readingFormula narrowReading = narrowBody

broadReadingDistinctFromNarrow :
  ¬ (ScopeReading.broadDeMorganReading ≡ ScopeReading.narrowReading)
broadReadingDistinctFromNarrow ()

-----------------------------------------------------------------------
-- Semantic fibre: both candidates retained, scope unresolved upstream.
-----------------------------------------------------------------------

candidateFibre : Candidate.CandidateSemanticFibre
candidateFibre =
  Candidate.candidateSemanticFibre
    (negBroadCandidate ∷ negNarrowCandidate ∷ [])
    ("negated-coordination scope fibre: broad-de-Morgan vs narrow; "
      ++ "parser 'neg'->'mutate' does not settle scope")

-----------------------------------------------------------------------
-- Dialectic review atoms over the two parser-supported readings.
--
-- d_L = disposition of reading A (broad), d_R = disposition of reading B
-- (narrow), d_S = synthesis/adjudication coordinate.  Two concrete atoms are
-- shown: a first-pass review that suspends the synthesis, and a later revised
-- review that reconverges on the same final formula.
-----------------------------------------------------------------------

firstPass369 : Bridge369.SpacyCandidateDialectic369Atom
firstPass369 =
  Bridge369.makeSpacyCandidateDialectic369Atom
    negBroadCandidate negNarrowCandidate
    suspendCandidate admitCandidate suspendCandidate
    "first-pass-review: suspend synthesis pending scope evidence"
    "review-pass-1"

revised369 : Bridge369.SpacyCandidateDialectic369Atom
revised369 =
  Bridge369.makeSpacyCandidateDialectic369Atom
    negBroadCandidate negNarrowCandidate
    rejectCandidate admitCandidate admitCandidate
    "revised-review: resolve broad reading away, keep the narrow residue"
    "review-pass-2"

-- The two review histories are genuinely different on the left disposition.
firstPassDifferentFromRevised :
  ¬ (Bridge369.leftDisposition firstPass369 ≡ Bridge369.leftDisposition revised369)
firstPassDifferentFromRevised ()

-----------------------------------------------------------------------
-- Reviewed evidential PNF, shared by both review histories.
--
-- The final logical reading is the de Morgan conjunctive residue
--
--     psi = (not Mutate(state)) /\ (not Promote(tasks))
--
-- Broad de Morgan and narrow routes both arrive here under that normal form;
-- the route metadata differs even though the formula is the same.
-----------------------------------------------------------------------

finalFormula : Formula
finalFormula = notF mutateSurface ∧ notF promoteSurface

assertionScope : Evidence.AssertionScope
assertionScope =
  Evidence.assertionScope
    "SensibLaw runtime consumers"
    "SensibLaw StatiBaker runtime"
    "mutation / promotion degree"
    "no explicit comparator"
    "state transcription and task promotion"
    "document time"

mutationPredicate : Evidence.PredicateAtom
mutationPredicate =
  Evidence.predicateAtom "mutate-state" Evidence.outcomePredicate
    "runtime-state × event" "the runtime state is not mutated"

promotionPredicate : Evidence.PredicateAtom
promotionPredicate =
  Evidence.predicateAtom "promote-task" Evidence.outcomePredicate
    "task × event" "tasks are not promoted by itself"

reviewedAssertion : Evidence.PredicateNormalAssertion
reviewedAssertion =
  Evidence.predicateNormalAssertion
    "spacy-negated-coordination-trace-v1"
    ("It does not mutate live StatiBaker state, mark work complete, "
      ++ "or promote tasks by itself.")
    Evidence.studyPopulationQ
    Evidence.descriptiveF
    assertionScope
    (mutationPredicate ∷ promotionPredicate ∷ [])
    "materialised spaCy parse of SensibLaw README; scope resolution receipt-bearing"

-----------------------------------------------------------------------
-- Object-logic readbacks: both histories derive the SAME final formula.
-----------------------------------------------------------------------

interpretation : Logic.EvidencePNFLogicalInterpretation reviewedAssertion
interpretation =
  Logic.evidencePNFLogicalInterpretation
    finalFormula
    "predicates Mutate/Promote -> atoms"
    "negation carries a scope-review residual"
    "broad de Morgan or narrow conjunctive residue agree at the formula level"
    "descriptive; causal promotion remains blocked"
    "review:spacy-negated-coordination-interpretation-v1"

readbackFinal :
  Logic.LogicalToEvidenceReadback interpretation finalFormula
readbackFinal =
  Logic.logicalToEvidenceReadback
    (assumption here)
    "readback: interpreted PNF derives the conjunctive residue"
    "same empirical scope (descriptive, no strengthening)"
    "no causal/population strengthening certificate"

-----------------------------------------------------------------------
-- Modus ponens is oblivious to the 369 chart coordinate.
-----------------------------------------------------------------------

mpPremise : Formula
mpPremise = coordinationSurface ⇒ broadBody

mpContext : List Formula
mpContext = mpPremise ∷ coordinationSurface ∷ []

mpUnderFirstPass369 :
  mpContext ⊢ broadBody
mpUnderFirstPass369 =
  Capstone.modusPonensIgnores369Chart
    firstPass369
    (assumption here)
    (assumption (there here))

mpUnderRevised369 :
  mpContext ⊢ broadBody
mpUnderRevised369 =
  Capstone.modusPonensIgnores369Chart
    revised369
    (assumption here)
    (assumption (there here))

-- The concrete Chart argument is irrelevant to the derivation term, so both
-- derivations are definitionally the same proof despite different charts.
sameProofShapeUnderDifferentCharts :
  mpUnderFirstPass369 ≡ mpUnderRevised369
sameProofShapeUnderDifferentCharts = refl

-----------------------------------------------------------------------
-- Empirical-strength promotion is still blocked under the 369 chart.
-----------------------------------------------------------------------

causalStillBlockedUnderCoordination :
  Logic.promotionAuthority Evidence.strengthensCausalForce
  ≡ Logic.requiresAdditionalEmpiricalEvidence
causalStillBlockedUnderCoordination = refl

populationStillBlockedUnderCoordination :
  Logic.promotionAuthority Evidence.widensPopulation
  ≡ Logic.requiresAdditionalEmpiricalEvidence
populationStillBlockedUnderCoordination = refl

-----------------------------------------------------------------------
-- Hard boundaries for this materialised coordinate specimen.
-----------------------------------------------------------------------

record NegatedCoordinationScopeTraceBoundary : Set where
  constructor negatedCoordinationScopeTraceBoundary
  field
    specimenIsMaterialisedSpacyRun : Bool
    specimenIsMaterialisedSpacyRunIsTrue :
      specimenIsMaterialisedSpacyRun ≡ true

    negEdgeSettlesFinalScope : Bool
    negEdgeSettlesFinalScopeIsFalse : negEdgeSettlesFinalScope ≡ false

    flatParseChoosesBroadOrNarrow : Bool
    flatParseChoosesBroadOrNarrowIsFalse :
      flatParseChoosesBroadOrNarrow ≡ false

    parserDependencyIsWorldSemantics : Bool
    parserDependencyIsWorldSemanticsIsFalse :
      parserDependencyIsWorldSemantics ≡ false

    parsedNegationIsCounterposition : Bool
    parsedNegationIsCounterpositionIsFalse :
      parsedNegationIsCounterposition ≡ false

    neutralReviewCoordinateIsFalsity : Bool
    neutralReviewCoordinateIsFalsityIsFalse :
      neutralReviewCoordinateIsFalsity ≡ false

    sameFinalFormulaImpliesSameHistory : Bool
    sameFinalFormulaImpliesSameHistoryIsFalse :
      sameFinalFormulaImpliesSameHistory ≡ false

    logicalProofIsEmpiricalStrengthening : Bool
    logicalProofIsEmpiricalStrengtheningIsFalse :
      logicalProofIsEmpiricalStrengthening ≡ false

canonicalNegatedCoordinationScopeTraceBoundary :
  NegatedCoordinationScopeTraceBoundary
canonicalNegatedCoordinationScopeTraceBoundary =
  negatedCoordinationScopeTraceBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
