module DASHI.Cognition.PNF.SensibLawScopeCompositionLiveRegressionExact where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.NumericAuthority as Numeric
import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.SpacyExecutableSemanticRuleBankExact as RuleBank
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawScopeCompositionBidiExact as Scope

------------------------------------------------------------------------
-- LIVE SPACY -> EXECUTABLE RULE -> SCOPE RECEIPT REGRESSION
--
-- Numeric ids are deliberately opaque parser observations.  No orthographic
-- string is inspected.  Rule admission is paid by dependency-shape equality;
-- semantic force/scope is then paid by separate resolver receipts.
------------------------------------------------------------------------

headObservation : Spacy.SpacyTokenObservation
headObservation =
  Spacy.spacyTokenObservation
    (Numeric.tokenId 1)
    (Numeric.sentenceId 1)
    0
    0 4
    (Numeric.symbolId 100)
    (Spacy.parserLemma (Numeric.symbolId 101))
    (Spacy.annotationPresent (Numeric.symbolId 102))
    (Spacy.annotationPresent (Numeric.symbolId 103))
    (Spacy.annotationPresent (Numeric.symbolId 104))
    Spacy.nothing
    Spacy.declaredSelfHead

modalObservation : Spacy.SpacyTokenObservation
modalObservation =
  Spacy.spacyTokenObservation
    (Numeric.tokenId 2)
    (Numeric.sentenceId 1)
    1
    5 9
    (Numeric.symbolId 110)
    (Spacy.parserLemma (Numeric.symbolId 111))
    (Spacy.annotationPresent (Numeric.symbolId 112))
    (Spacy.annotationPresent (Numeric.symbolId 113))
    (Spacy.annotationPresent (Numeric.symbolId 114))
    Spacy.nothing
    (Spacy.declaredHeadAt 0 4)

negObservation : Spacy.SpacyTokenObservation
negObservation =
  Spacy.spacyTokenObservation
    (Numeric.tokenId 3)
    (Numeric.sentenceId 1)
    2
    10 13
    (Numeric.symbolId 120)
    (Spacy.parserLemma (Numeric.symbolId 121))
    (Spacy.annotationPresent (Numeric.symbolId 122))
    (Spacy.annotationPresent (Numeric.symbolId 123))
    (Spacy.annotationPresent (Numeric.symbolId 124))
    Spacy.nothing
    (Spacy.declaredHeadAt 0 4)

temporalObservation : Spacy.SpacyTokenObservation
temporalObservation =
  Spacy.spacyTokenObservation
    (Numeric.tokenId 4)
    (Numeric.sentenceId 1)
    3
    14 20
    (Numeric.symbolId 130)
    (Spacy.parserLemma (Numeric.symbolId 131))
    (Spacy.annotationPresent (Numeric.symbolId 132))
    (Spacy.annotationPresent (Numeric.symbolId 133))
    (Spacy.annotationPresent (Numeric.symbolId 134))
    Spacy.nothing
    (Spacy.declaredHeadAt 0 4)

conditionalObservation : Spacy.SpacyTokenObservation
conditionalObservation =
  Spacy.spacyTokenObservation
    (Numeric.tokenId 5)
    (Numeric.sentenceId 1)
    4
    21 27
    (Numeric.symbolId 140)
    (Spacy.parserLemma (Numeric.symbolId 141))
    (Spacy.annotationPresent (Numeric.symbolId 142))
    (Spacy.annotationPresent (Numeric.symbolId 143))
    (Spacy.annotationPresent (Numeric.symbolId 144))
    Spacy.nothing
    (Spacy.declaredHeadAt 0 4)

modalWitness : Candidate.DependencyWitness
modalWitness =
  Candidate.dependencyWitness
    modalObservation headObservation Candidate.modalAuxiliary
    "committed dependency:modal"

negWitness : Candidate.DependencyWitness
negWitness =
  Candidate.dependencyWitness
    negObservation headObservation Candidate.negation
    "committed dependency:neg"

temporalWitness : Candidate.DependencyWitness
temporalWitness =
  Candidate.dependencyWitness
    temporalObservation headObservation Candidate.temporalModifier
    "committed dependency:temporal"

conditionalWitness : Candidate.DependencyWitness
conditionalWitness =
  Candidate.dependencyWitness
    conditionalObservation headObservation Candidate.unresolvedDependency
    "committed dependency:conditional-marker"

modalAdmission : RuleBank.ShapeAdmission modalWitness Candidate.modalAuxiliary
modalAdmission = RuleBank.shapeAdmission refl "rulebank-v1" "dependency-shape:modal"

negAdmission : RuleBank.ShapeAdmission negWitness Candidate.negation
negAdmission = RuleBank.shapeAdmission refl "rulebank-v1" "dependency-shape:neg"

temporalAdmission :
  RuleBank.ShapeAdmission temporalWitness Candidate.temporalModifier
temporalAdmission =
  RuleBank.shapeAdmission refl "rulebank-v1" "dependency-shape:temporal"

bodyFormula : Candidate.Formula
bodyFormula =
  Candidate.atom "Act"
    (Candidate.eventTerm "event:scope-demo" ∷
     Candidate.entityTerm "entity:A" ∷ [])

conditionFormula : Candidate.Formula
conditionFormula =
  Candidate.atom "Condition"
    (Candidate.eventTerm "event:condition-demo" ∷ [])

modalCandidate : Candidate.CandidateSemanticFragment
modalCandidate =
  RuleBank.modalQualificationRule
    modalWitness modalAdmission "opaque-modal-reading" "event:scope-demo"

negCandidate : Candidate.CandidateSemanticFragment
negCandidate =
  RuleBank.negationScopeRule negWitness negAdmission bodyFormula

temporalCandidate : Candidate.CandidateSemanticFragment
temporalCandidate =
  RuleBank.temporalQualificationRule
    temporalWitness temporalAdmission "event:scope-demo" "opaque-time-reading"

conditionalComposition : RuleBank.ConditionalComposition
conditionalComposition =
  RuleBank.conditionalComposition
    conditionFormula
    bodyFormula
    (conditionalWitness ∷ [])
    "typed conditional-marker receipt"
    "conditional-scope resolver"

conditionalFormula : Candidate.Formula
conditionalFormula = RuleBank.conditionalRule conditionalComposition

------------------------------------------------------------------------
-- Semantic resolution receipts are separate from parser admission.
------------------------------------------------------------------------

record ModalSemanticResolution : Set where
  constructor modalSemanticResolution
  field
    candidate : Candidate.CandidateSemanticFragment
    candidateIsModal : Candidate.kind candidate ≡ Candidate.modalityFragment
    modalityKind : Status.ModalityKind
    force : Status.ModalForce
    scope : Status.ScopeStatus
    resolverReference : String

record NegationSemanticResolution : Set where
  constructor negationSemanticResolution
  field
    candidate : Candidate.CandidateSemanticFragment
    candidateIsNegation : Candidate.kind candidate ≡ Candidate.negationFragment
    scope : Status.ScopeStatus
    resolverReference : String

record TemporalSemanticResolution : Set where
  constructor temporalSemanticResolution
  field
    candidate : Candidate.CandidateSemanticFragment
    candidateIsTemporal : Candidate.kind candidate ≡ Candidate.temporalFragment
    relation : Status.TemporalRelationKind
    scope : Status.ScopeStatus
    resolverReference : String

record ConditionalSemanticResolution : Set where
  constructor conditionalSemanticResolution
  field
    composition : RuleBank.ConditionalComposition
    kind : Status.ConditionKind
    scope : Status.ScopeStatus
    resolverReference : String

open ModalSemanticResolution public
open NegationSemanticResolution public
open TemporalSemanticResolution public
open ConditionalSemanticResolution public

modalResolution : ModalSemanticResolution
modalResolution =
  modalSemanticResolution
    modalCandidate refl
    Status.deontic Status.obligation Status.scopeResolved
    "governed modal interpretation fixture"

negResolution : NegationSemanticResolution
negResolution =
  negationSemanticResolution
    negCandidate refl Status.scopeResolved
    "governed negation-scope fixture"

temporalResolution : TemporalSemanticResolution
temporalResolution =
  temporalSemanticResolution
    temporalCandidate refl Status.referenceTime Status.scopeResolved
    "governed temporal-anchor fixture"

conditionResolution : ConditionalSemanticResolution
conditionResolution =
  conditionalSemanticResolution
    conditionalComposition Status.unlessCondition Status.scopeResolved
    "governed conditional-scope fixture"

------------------------------------------------------------------------
-- All four axes are welded over the same literal proposition/event refs.
------------------------------------------------------------------------

scopeDemoProposition : Status.PropositionStatusProduct
scopeDemoProposition =
  Status.propositionStatusProduct
    "proposition:scope-demo"
    Status.assertedBySource
    Status.truthUnresolved
    Status.propositionSource
    Status.sourceEvidence
      |>λ
  where
    infixl 0 |>λ
    _|>λ : Status.EvidenceKind →
      Status.PropositionStatusProduct
    _|>λ evidenceKind =
      Status.propositionStatusProduct
        "proposition:scope-demo"
        Status.assertedBySource
        Status.truthUnresolved
        Status.propositionSource
        Status.evidenceNeutral
        evidenceKind
        Status.modalityKindUnresolved
        Status.modalForceUnresolved
        Status.scopeUnresolved

scopeDemoEvent : Status.EventStatusProduct
scopeDemoEvent =
  Status.eventStatusProduct
    "event:scope-demo"
    Status.assertedOccurrence
    Status.eventTime
    Status.scopeUnresolved

liveScopeComposition : Scope.ScopeCompositionReceipt
liveScopeComposition =
  Scope.scopeCompositionReceipt
    scopeDemoProposition
    scopeDemoEvent
    conditionalFormula
    (modalWitness ∷ negWitness ∷ temporalWitness ∷ conditionalWitness ∷ [])
    (ModalSemanticResolution.modalityKind modalResolution)
    (ModalSemanticResolution.force modalResolution)
    (ModalSemanticResolution.scope modalResolution)
    (NegationSemanticResolution.scope negResolution)
    (ConditionalSemanticResolution.kind conditionResolution)
    (ConditionalSemanticResolution.scope conditionResolution)
    (TemporalSemanticResolution.relation temporalResolution)
    (TemporalSemanticResolution.scope temporalResolution)
    "joint live scope regression"
    false
    false

liveScopeQualifiedOccurrence : Scope.ScopeQualifiedOccurrence
liveScopeQualifiedOccurrence =
  Scope.preserveReferenceScopeQualification
    liveScopeComposition
    Status.conditionalOccurrence
    Status.hypotheticalProposition
    Status.truthUnresolved

liveScopeTruthStillUnresolved :
  Scope.resultingTruth liveScopeQualifiedOccurrence ≡ Status.truthUnresolved
liveScopeTruthStillUnresolved = refl

------------------------------------------------------------------------
-- Regression boundaries.
------------------------------------------------------------------------

data ParserAdmissionIsModalResolution : Set where
data ResolvedScopeIsOccurrenceAdmission : Set where

a parserAdmissionDoesNotResolveModalForce : ParserAdmissionIsModalResolution → ⊥
a parserAdmissionDoesNotResolveModalForce ()

resolvedScopeDoesNotAdmitOccurrence : ResolvedScopeIsOccurrenceAdmission → ⊥
resolvedScopeDoesNotAdmitOccurrence ()
