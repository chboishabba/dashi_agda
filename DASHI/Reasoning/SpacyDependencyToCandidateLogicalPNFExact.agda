module DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as EvidencePNF

------------------------------------------------------------------------
-- BIDI PARSER OBSERVATION -> CANDIDATE SEMANTIC PNF
--
-- This is deliberately not a parser-is-semantics compiler.  A spaCy
-- dependency observation licenses only a candidate semantic fragment.  The
-- reverse direction records which parser observations would witness a chosen
-- fragment.  Ambiguity is retained as a fibre until a separate resolution
-- receipt selects an admissible reading.
------------------------------------------------------------------------

data Term : Set where
  entityTerm eventTerm variableTerm literalTerm : String → Term

data Formula : Set where
  atom : String → List Term → Formula
  _∧_ _∨_ _⇒_ : Formula → Formula → Formula
  notF : Formula → Formula
  existsF forallF : String → String → Formula → Formula

infixr 6 _∧_
infixr 5 _∨_
infixr 4 _⇒_

data DependencyShape : Set where
  nominalSubject
  directObject
  passiveSubject
  adjectivalModifier
  nominalModifier
  conjunction
  negation
  modalAuxiliary
  determiner
  temporalModifier
  unresolvedDependency
  : DependencyShape

record DependencyWitness : Set where
  constructor dependencyWitness
  field
    dependent : Spacy.SpacyTokenObservation
    head : Spacy.SpacyTokenObservation
    shape : DependencyShape
    parserDependencyReference : String

open DependencyWitness public

data SemanticFragmentKind : Set where
  actorFragment
  patientFragment
  propertyFragment
  relationFragment
  conjunctionFragment
  negationFragment
  modalityFragment
  quantifierFragment
  temporalFragment
  unresolvedFragment
  : SemanticFragmentKind

record CandidateSemanticFragment : Set where
  constructor candidateSemanticFragment
  field
    fragmentKey : String
    kind : SemanticFragmentKind
    formula : Formula
    forwardWitness : DependencyWitness
    reading : String
    confidenceOrRankingReference : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open CandidateSemanticFragment public

------------------------------------------------------------------------
-- BIDI direction.  Forward extraction and reverse support are constructor
-- distinct.  Reverse support never means the dependency parse uniquely
-- determines the semantic reading.
------------------------------------------------------------------------

record ParserSemanticBidi : Set₁ where
  constructor parserSemanticBidi
  field
    forwardCandidates : DependencyWitness → List CandidateSemanticFragment
    reverseSupport : CandidateSemanticFragment → List DependencyWitness
    forwardRuleReference : String
    reverseRuleReference : String

open ParserSemanticBidi public

------------------------------------------------------------------------
-- Ambiguity remains a fibre.  Selecting one candidate requires an explicit
-- resolution receipt and retains the rejected/alternative readings.
------------------------------------------------------------------------

record CandidateSemanticFibre : Set where
  constructor candidateSemanticFibre
  field
    candidates : List CandidateSemanticFragment
    fibreReference : String

open CandidateSemanticFibre public

record SemanticResolutionReceipt (fibre : CandidateSemanticFibre) : Set₁ where
  constructor semanticResolutionReceipt
  field
    selected : CandidateSemanticFragment
    selectedInFibreReference : String
    retainedAlternatives : List CandidateSemanticFragment
    scopeResolutionReference : String
    entityResolutionReference : String
    reviewerOrResolverReference : String

open SemanticResolutionReceipt public

------------------------------------------------------------------------
-- Correspondence into the evidence-facing PNF remains proof-relevant.
-- A resolved candidate can propose a quantifier, inferential force, scope and
-- predicate atoms, but each proposal carries an independent correspondence
-- reference.  Nothing here manufactures world truth.
------------------------------------------------------------------------

record ResolvedCandidateToEvidencePNF
    {fibre : CandidateSemanticFibre}
    (resolution : SemanticResolutionReceipt fibre)
    (assertion : EvidencePNF.PredicateNormalAssertion) : Set₁ where
  constructor resolvedCandidateToEvidencePNF
  field
    formulaCorrespondenceReference : String
    predicateAtomCorrespondenceReference : String
    quantifierCorrespondenceReference : String
    inferentialForceCorrespondenceReference : String
    scopeCorrespondenceReference : String
    worldIdentityStillExternal : Bool
    worldIdentityStillExternalIsTrue : worldIdentityStillExternal ≡ true

open ResolvedCandidateToEvidencePNF public

------------------------------------------------------------------------
-- Canonical rule schemas.  These are intentionally syntactic candidates.
------------------------------------------------------------------------

subjectCandidate : DependencyWitness → String → String → CandidateSemanticFragment
subjectCandidate witness eventName entityName =
  candidateSemanticFragment
    "spacy-nsubj-candidate"
    actorFragment
    (atom "Actor" (eventTerm eventName ∷ entityTerm entityName ∷ []))
    witness
    "nominal subject proposes an actor/event relation"
    "dependency-rule:nsubj->Actor"
    true refl

objectCandidate : DependencyWitness → String → String → CandidateSemanticFragment
objectCandidate witness eventName entityName =
  candidateSemanticFragment
    "spacy-obj-candidate"
    patientFragment
    (atom "Patient" (eventTerm eventName ∷ entityTerm entityName ∷ []))
    witness
    "direct object proposes a patient/event relation"
    "dependency-rule:obj->Patient"
    true refl

negationCandidate : DependencyWitness → Formula → CandidateSemanticFragment
negationCandidate witness body =
  candidateSemanticFragment
    "spacy-neg-candidate"
    negationFragment
    (notF body)
    witness
    "dependency negation proposes scoped logical negation; scope remains reviewable"
    "dependency-rule:neg->notF"
    true refl

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

record SpacySemanticBoundary : Set where
  constructor spacySemanticBoundary
  field
    dependencyUniquelyDeterminesSemantics : Bool
    dependencyUniquelyDeterminesSemanticsIsFalse :
      dependencyUniquelyDeterminesSemantics ≡ false
    candidateFragmentIsWorldFact : Bool
    candidateFragmentIsWorldFactIsFalse : candidateFragmentIsWorldFact ≡ false
    ambiguityMayBeSilentlyDropped : Bool
    ambiguityMayBeSilentlyDroppedIsFalse : ambiguityMayBeSilentlyDropped ≡ false
    reverseSupportMeansSemanticEquivalence : Bool
    reverseSupportMeansSemanticEquivalenceIsFalse :
      reverseSupportMeansSemanticEquivalence ≡ false
    resolvedCandidateCanFeedEvidencePNF : Bool
    resolvedCandidateCanFeedEvidencePNFIsTrue :
      resolvedCandidateCanFeedEvidencePNF ≡ true

canonicalSpacySemanticBoundary : SpacySemanticBoundary
canonicalSpacySemanticBoundary =
  spacySemanticBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
