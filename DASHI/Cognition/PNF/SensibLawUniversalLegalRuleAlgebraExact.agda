module DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact where

------------------------------------------------------------------------
-- UNIVERSAL PROOF-RELEVANT LEGAL RULE ALGEBRA
--
-- This is the missing middle between the existing SensibLaw ontology and the
-- issue-indexed adjudicative/search machinery:
--
--   full legal graph -> issue projection -> derivation / cut -> WrongType use.
--
-- It is deliberately source-form neutral. Constitution, statute, regulation,
-- case law, treaty, custom and community rule are all admitted through the
-- existing SensibLaw ontology; proposition-level authority role is separate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology

------------------------------------------------------------------------
-- Small reusable proof infrastructure.
------------------------------------------------------------------------

infix 4 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

data All {A : Set} (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

------------------------------------------------------------------------
-- Source FORM and proposition AUTHORITY ROLE are orthogonal.
--
-- A case is a source form. Ratio, dictum, factual finding, submission, etc are
-- roles of propositions within source material. They must not be collapsed.
------------------------------------------------------------------------

data AuthorityRole : Set where
  constitutionalRuleRole : AuthorityRole
  legislativeRuleRole : AuthorityRole
  delegatedRuleRole : AuthorityRole
  bindingRatioRole : AuthorityRole
  persuasiveRatioRole : AuthorityRole
  dictumRole : AuthorityRole
  concurrenceRole : AuthorityRole
  dissentRole : AuthorityRole
  adjudicatedFactRole : AuthorityRole
  partySubmissionRole : AuthorityRole
  judicialPolicyReasonRole : AuthorityRole
  interpretiveInputRole : AuthorityRole
  empiricalEvidenceRole : AuthorityRole
  communityNormRole : AuthorityRole
  dashReconstructionRole : AuthorityRole


record LegalSourceRef : Set where
  constructor legal-source-ref
  field
    source : Ontology.LegalSource
    authorOrInstitution : String
    title : String
    stableIdentifier : String

open LegalSourceRef public

------------------------------------------------------------------------
-- Typed legal propositions replace opaque premise/conclusion strings.
------------------------------------------------------------------------

data PropositionKind : Set where
  factualFeature : PropositionKind
  relationalFeature : PropositionKind
  doctrinalPredicate : PropositionKind
  institutionalConstraint : PropositionKind
  wrongElementPredicate : PropositionKind
  remedyConstraint : PropositionKind
  jurisdictionPredicate : PropositionKind
  temporalPredicate : PropositionKind
  authorityPredicate : PropositionKind
  otherLegalPredicate : PropositionKind


record LegalProposition : Set where
  constructor legal-proposition
  field
    propositionId : Ontology.StableId
    propositionKind : PropositionKind
    subjectReference : Ontology.StableId
    objectReference : Ontology.StableId
    legalSystem : Ontology.StableId
    statement : String

open LegalProposition public

record LegalFact : Set where
  constructor legal-fact
  field
    proposition : LegalProposition
    evidenceReference : String
    sourceReference : String

open LegalFact public

------------------------------------------------------------------------
-- Rules own premises, conclusion, exceptions and defeaters as propositions.
------------------------------------------------------------------------

record LegalRule : Set where
  constructor legal-rule
  field
    ruleId : Ontology.StableId
    premises : List LegalProposition
    conclusion : LegalProposition
    exceptions : List LegalProposition
    defeaters : List LegalProposition
    sourceRef : LegalSourceRef
    authorityRole : AuthorityRole
    temporalScope : String
    jurisdictionScope : String

open LegalRule public

record LegalGraph : Set where
  constructor legal-graph
  field
    rules : List LegalRule
    sourceUniverse : List LegalSourceRef

open LegalGraph public

------------------------------------------------------------------------
-- Facts are proposition-indexed witnesses, not strings.
------------------------------------------------------------------------

record FactSet : Set where
  constructor fact-set
  field
    facts : List LegalProposition

open FactSet public

------------------------------------------------------------------------
-- Proof-relevant derivation.
--
-- Enabled is parameterised so counterfactual edge removal/minimal cuts can be
-- represented without destructively editing the graph.
------------------------------------------------------------------------

data Derivation
  (graph : LegalGraph)
  (factSet : FactSet)
  (Enabled : LegalRule → Set)
  : LegalProposition → Set where

  fromFact :
    ∀ {p} →
    p ∈ facts factSet →
    Derivation graph factSet Enabled p

  byRule :
    ∀ {r} →
    r ∈ rules graph →
    Enabled r →
    All (Derivation graph factSet Enabled) (premises r) →
    (All (λ e → Derivation graph factSet Enabled e → ⊥) (exceptions r)) →
    (All (λ d → Derivation graph factSet Enabled d → ⊥) (defeaters r)) →
    Derivation graph factSet Enabled (conclusion r)

Reachable : LegalGraph → FactSet → LegalProposition → Set
Reachable graph facts goal = Derivation graph facts (λ _ → ⊤) goal

------------------------------------------------------------------------
-- Universal graph versus issue-specific active graph.
--
-- Issue-specific reasoning is a projection of the universal graph, not another
-- legal pipeline. Relevance is proof-bearing and consumer/query supplied.
------------------------------------------------------------------------

record LegalIssue : Set where
  constructor legal-issue
  field
    issueId : Ontology.StableId
    target : LegalProposition
    issueSystem : Ontology.StableId
    issueLabel : String

open LegalIssue public

record IssueProjection (graph : LegalGraph) (issue : LegalIssue) : Set where
  constructor issue-projection
  field
    activeRule : LegalRule → Set
    activeRuleComesFromUniversalGraph :
      ∀ {r} → activeRule r → r ∈ rules graph
    targetPreserved : LegalProposition
    targetPreservedIsIssueTarget : targetPreserved ≡ target issue

open IssueProjection public

IssueReachable :
  (graph : LegalGraph) →
  FactSet →
  (issue : LegalIssue) →
  IssueProjection graph issue →
  Set
IssueReachable graph facts issue projection =
  Derivation graph facts (IssueProjection.activeRule projection) (target issue)

------------------------------------------------------------------------
-- Counterfactual cuts and proof-relevant minimality.
------------------------------------------------------------------------

record CutSet (graph : LegalGraph) (facts : FactSet) (goal : LegalProposition) : Set where
  constructor cut-set
  field
    cutRules : List LegalRule
    blocksGoal :
      Derivation graph facts
        (λ r → r ∈ cutRules → ⊥)
        goal
      → ⊥

open CutSet public

record MinimalCut
  (graph : LegalGraph)
  (facts : FactSet)
  (goal : LegalProposition)
  : Set where
  constructor minimal-cut
  field
    cut : CutSet graph facts goal
    everyCutRuleIsEssential :
      ∀ {r} →
      r ∈ CutSet.cutRules cut →
      Derivation graph facts
        (λ s → (s ≡ r) ⊎ (s ∈ CutSet.cutRules cut → ⊥))
        goal

open MinimalCut public

------------------------------------------------------------------------
-- Minimal transformation is now tied to typed propositions/rules.
------------------------------------------------------------------------

data RuleTransformationKind : Set where
  addRule : RuleTransformationKind
  removeRule : RuleTransformationKind
  narrowRulePremises : RuleTransformationKind
  widenRulePremises : RuleTransformationKind
  addException : RuleTransformationKind
  removeException : RuleTransformationKind
  addDefeater : RuleTransformationKind
  removeDefeater : RuleTransformationKind
  alterAuthorityRole : RuleTransformationKind
  alterJurisdictionScope : RuleTransformationKind
  alterTemporalScope : RuleTransformationKind


record LegalTransformation : Set where
  constructor legal-transformation
  field
    transformedRule : LegalRule
    transformationKind : RuleTransformationKind
    changedProposition : LegalProposition
    proposedAuthority : LegalSourceRef
    legalAvailabilityStillRequiresProof : Bool

open LegalTransformation public

record MinimalTransformationResult
  (graph : LegalGraph)
  (facts : FactSet)
  (goal : LegalProposition)
  : Set where
  constructor minimal-transformation-result
  field
    obstruction : MinimalCut graph facts goal
    transformation : LegalTransformation
    reopenedDerivation : Set

open MinimalTransformationResult public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SourceFormDeterminesPropositionRole : Set where
data IssueProjectionCreatesNewRule : Set where
data DerivationCreatesAuthority : Set where
data NormativeDesirabilityIsLegalFact : Set where

sourceFormDoesNotDetermineRole : SourceFormDeterminesPropositionRole → ⊥
sourceFormDoesNotDetermineRole ()

projectionDoesNotCreateRule : IssueProjectionCreatesNewRule → ⊥
projectionDoesNotCreateRule ()

derivationDoesNotCreateAuthority : DerivationCreatesAuthority → ⊥
derivationDoesNotCreateAuthority ()

normativeDesirabilityDoesNotBecomeFact : NormativeDesirabilityIsLegalFact → ⊥
normativeDesirabilityDoesNotBecomeFact ()
