module DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as EvidencePNF

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
  nominalSubject directObject passiveSubject adjectivalModifier nominalModifier
  conjunction negation modalAuxiliary determiner temporalModifier
  clausalComplement openClausalComplement adverbialClause clausalModifier relativeClause
  unresolvedDependency : DependencyShape

record DependencyWitness : Set where
  constructor dependencyWitness
  field
    dependent : Spacy.SpacyTokenObservation
    head : Spacy.SpacyTokenObservation
    shape : DependencyShape
    parserDependencyReference : String
open DependencyWitness public

data SemanticFragmentKind : Set where
  actorFragment patientFragment propertyFragment relationFragment conjunctionFragment
  negationFragment modalityFragment quantifierFragment temporalFragment
  contentClauseFragment clauseAttachmentFragment unresolvedFragment : SemanticFragmentKind

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

record ParserSemanticBidi : Set₁ where
  constructor parserSemanticBidi
  field
    forwardCandidates : DependencyWitness → List CandidateSemanticFragment
    reverseSupport : CandidateSemanticFragment → List DependencyWitness
    forwardRuleReference : String
    reverseRuleReference : String
open ParserSemanticBidi public

record CandidateSemanticFibre : Set where
  constructor candidateSemanticFibre
  field candidates : List CandidateSemanticFragment; fibreReference : String
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

record ResolvedCandidateToEvidencePNF {fibre : CandidateSemanticFibre}
    (resolution : SemanticResolutionReceipt fibre)
    (assertion : EvidencePNF.PredicateNormalAssertion) : Set₁ where
  constructor resolvedCandidateToEvidencePNF
  field
    formulaCorrespondenceReference predicateAtomCorrespondenceReference : String
    quantifierCorrespondenceReference inferentialForceCorrespondenceReference : String
    scopeCorrespondenceReference : String
    worldIdentityStillExternal : Bool
    worldIdentityStillExternalIsTrue : worldIdentityStillExternal ≡ true
open ResolvedCandidateToEvidencePNF public

subjectCandidate : DependencyWitness → String → String → CandidateSemanticFragment
subjectCandidate witness eventName entityName = candidateSemanticFragment
  "spacy-nsubj-candidate" actorFragment
  (atom "Actor" (eventTerm eventName ∷ entityTerm entityName ∷ [])) witness
  "nominal subject proposes an actor/event relation" "dependency-rule:nsubj->Actor" true refl

objectCandidate : DependencyWitness → String → String → CandidateSemanticFragment
objectCandidate witness eventName entityName = candidateSemanticFragment
  "spacy-obj-candidate" patientFragment
  (atom "Patient" (eventTerm eventName ∷ entityTerm entityName ∷ [])) witness
  "direct object proposes a patient/event relation" "dependency-rule:obj->Patient" true refl

negationCandidate : DependencyWitness → Formula → CandidateSemanticFragment
negationCandidate witness body = candidateSemanticFragment
  "spacy-neg-candidate" negationFragment (notF body) witness
  "dependency negation proposes scoped logical negation; scope remains reviewable"
  "dependency-rule:neg->notF" true refl

contentClauseCandidate : DependencyWitness → String → String → CandidateSemanticFragment
contentClauseCandidate witness governorEvent contentEvent = candidateSemanticFragment
  "spacy-content-clause-candidate" contentClauseFragment
  (atom "ContentClause" (eventTerm governorEvent ∷ eventTerm contentEvent ∷ [])) witness
  "clausal dependency proposes governor/content-event structure; discourse role remains unresolved"
  "dependency-rule:clausal->ContentClause" true refl

clauseAttachmentCandidate : DependencyWitness → String → String → String → CandidateSemanticFragment
clauseAttachmentCandidate witness relationName governorEvent clauseEvent = candidateSemanticFragment
  "spacy-clause-attachment-candidate" clauseAttachmentFragment
  (atom relationName (eventTerm governorEvent ∷ eventTerm clauseEvent ∷ [])) witness
  "clausal attachment proposes structural relation; legal/discourse interpretation remains unresolved"
  "dependency-rule:clausal-attachment" true refl

record SpacySemanticBoundary : Set where
  constructor spacySemanticBoundary
  field
    dependencyUniquelyDeterminesSemantics : Bool
    dependencyUniquelyDeterminesSemanticsIsFalse : dependencyUniquelyDeterminesSemantics ≡ false
    candidateFragmentIsWorldFact : Bool
    candidateFragmentIsWorldFactIsFalse : candidateFragmentIsWorldFact ≡ false
    ambiguityMayBeSilentlyDropped : Bool
    ambiguityMayBeSilentlyDroppedIsFalse : ambiguityMayBeSilentlyDropped ≡ false
    reverseSupportMeansSemanticEquivalence : Bool
    reverseSupportMeansSemanticEquivalenceIsFalse : reverseSupportMeansSemanticEquivalence ≡ false
    resolvedCandidateCanFeedEvidencePNF : Bool
    resolvedCandidateCanFeedEvidencePNFIsTrue : resolvedCandidateCanFeedEvidencePNF ≡ true
    clausalDependencyChoosesDiscourseRole : Bool
    clausalDependencyChoosesDiscourseRoleIsFalse : clausalDependencyChoosesDiscourseRole ≡ false
    clausalDependencyChoosesLegalStatus : Bool
    clausalDependencyChoosesLegalStatusIsFalse : clausalDependencyChoosesLegalStatus ≡ false

canonicalSpacySemanticBoundary : SpacySemanticBoundary
canonicalSpacySemanticBoundary = spacySemanticBoundary
  false refl false refl false refl false refl true refl false refl false refl
