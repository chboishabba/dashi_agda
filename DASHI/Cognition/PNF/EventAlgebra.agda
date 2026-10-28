{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.EventAlgebra where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Cognition.Utterance.LayeredMeaningCore as Utterance
import DASHI.Interop.SensibLawResidualLattice as Residual

data ParserProducer : Set where
  spaCyProducer : ParserProducer
  stanzaProducer : ParserProducer
  asrProducer : ParserProducer
  ruleProducer : ParserProducer
  udProducer uccaProducer mrsProducer amrProducer specialistProducer : ParserProducer

data CandidateValidity : Set where
  admissible : CandidateValidity
  invalid : CandidateValidity
  undetermined : CandidateValidity
  inapplicable : CandidateValidity

data SemanticRole : Set where
  actorRole : SemanticRole
  actionRole : SemanticRole
  objectRole : SemanticRole
  modalityRole : SemanticRole
  conditionRole : SemanticRole
  exceptionRole qualifierRole jurisdictionRole speakerRole : SemanticRole
  evidenceRole temporalRole provenanceRole unknownRole : SemanticRole

data RevisionKind : Set where
  parserCorrection : RevisionKind
  entityResolutionCorrection : RevisionKind
  translationRevision : RevisionKind
  legalReclassification evidenceStrengthening evidenceWeakening : RevisionKind
  contextualRevaluation contradictionRevision supersessionRevision : RevisionKind
  promotionRevision demotionRevision : RevisionKind

record SpanReceipt : Set where
  constructor spanReceipt
  field
    documentId : String
    characterStart characterEnd tokenStart tokenEnd : Nat
    spanProducer : ParserProducer
    dependencyOrRule : String

open SpanReceipt public

record ParserObservation : Set where
  constructor parserObservation
  field
    observationProducer : ParserProducer
    parserProfile : String
    languageTag : String
    sourceSpan : SpanReceipt
    observationLabel : String
    confidenceBand : Nat

open ParserObservation public

record EventPNF : Set where
  constructor eventPNF
  field
    sourceSurface : Utterance.SourceSurface
    utteranceDerivation : Utterance.PredicatePNF sourceSurface
    algebraicAtom : Residual.PredicatePNF
    semanticRoles : List SemanticRole
    parserObservations : List ParserObservation
    eventTime publicationTime observationTime ingestionTime : String
    contextLabel jurisdictionLabel : String
    revisionNumber : Nat
    parentRevisionId : String

open EventPNF public

record CandidatePNF : Set where
  constructor candidatePNF
  field
    event : EventPNF
    validity : CandidateValidity
    candidateReceipt : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open CandidatePNF public

record AdmissiblePNF : Set where
  constructor admissiblePNF
  field
    candidate : CandidatePNF
    candidateIsAdmissible : validity candidate ≡ admissible

open AdmissiblePNF public

record ResolvedPNF : Set where
  constructor resolvedPNF
  field
    selected : AdmissiblePNF
    retainedAlternatives : List CandidatePNF
    unresolvedResidual : Residual.ResidualLevel
    resolverReceipt selectorReceipt : String

open ResolvedPNF public

record PNFRevision : Set where
  constructor pnfRevision
  field
    before after : EventPNF
    revisionKind : RevisionKind
    revisionReceipt : String
    oldVersionRetained : Bool
    oldVersionRetainedIsTrue : oldVersionRetained ≡ true

open PNFRevision public

data ComparisonResult : Set where
  equivalent : ComparisonResult
  compatible : ComparisonResult
  contradictory : ComparisonResult
  residuallyDifferent : ComparisonResult
  noTypedMeet : ComparisonResult

comparisonFromResidual : Residual.ResidualLevel → ComparisonResult
comparisonFromResidual Residual.exact = equivalent
comparisonFromResidual Residual.partial = residuallyDifferent
comparisonFromResidual Residual.noTypedMeet = noTypedMeet
comparisonFromResidual Residual.contradiction = contradictory

comparePNF : EventPNF → EventPNF → ComparisonResult
comparePNF left right =
  comparisonFromResidual
    (Residual.computeResidual (algebraicAtom left) (algebraicAtom right))

------------------------------------------------------------------------
-- Pair-bound named incompatibility.
--
-- A noTypedMeet at the root join/composition surface is not emitted as a
-- shared string-only residual.  It carries the exact left/right EventPNF pair,
-- both structural signatures, an operation-local name, the canonical code,
-- and a proof that its residual is noTypedMeet.
--
-- This preserves strict pairwise independence: each failed pair owns its own
-- incompatibility value.  No join of separate noTypedMeet pairs is performed.
------------------------------------------------------------------------

record NamedIncompatibility : Set where
  constructor namedIncompatibility
  field
    incompatibilityName : String
    incompatibilityCode : String
    incompatibilityLeft : EventPNF
    incompatibilityRight : EventPNF
    leftStructuralSignature : Residual.StructuralSignature
    rightStructuralSignature : Residual.StructuralSignature
    incompatibilityResidual : Residual.ResidualLevel
    incompatibilityResidualIsNoTypedMeet :
      incompatibilityResidual ≡ Residual.noTypedMeet

open NamedIncompatibility public

namedNoTypedMeet :
  EventPNF → EventPNF → String → NamedIncompatibility
namedNoTypedMeet left right name =
  namedIncompatibility
    name
    "NO_TYPED_MEET"
    left
    right
    (Residual.PredicatePNF.structuralSignature (algebraicAtom left))
    (Residual.PredicatePNF.structuralSignature (algebraicAtom right))
    Residual.noTypedMeet
    refl

namedNoTypedMeetLeftIsInput :
  ∀ left right name →
  incompatibilityLeft (namedNoTypedMeet left right name) ≡ left
namedNoTypedMeetLeftIsInput left right name = refl

namedNoTypedMeetRightIsInput :
  ∀ left right name →
  incompatibilityRight (namedNoTypedMeet left right name) ≡ right
namedNoTypedMeetRightIsInput left right name = refl

namedNoTypedMeetResidualIsCanonical :
  ∀ left right name →
  incompatibilityResidual (namedNoTypedMeet left right name)
    ≡ Residual.noTypedMeet
namedNoTypedMeetResidualIsCanonical left right name = refl

data PNFOperationResult : Set where
  operationSuccess : EventPNF → PNFOperationResult
  operationResidual : Residual.ResidualLevel → String → PNFOperationResult
  operationIncompatibility : NamedIncompatibility → PNFOperationResult
  operationUndetermined : String → PNFOperationResult
  operationInapplicable : String → PNFOperationResult

record AlternativeFibre : Set where
  constructor alternativeFibre
  field
    alternatives : List CandidatePNF
    enumerationReceipt : String

open AlternativeFibre public

record TypedComposition : Set where
  constructor typedComposition
  field
    left right : EventPNF
    result : PNFOperationResult
    compositionReceipt : String

open TypedComposition public

composeByResidual : EventPNF → EventPNF → String → TypedComposition
composeByResidual left right receipt with
  Residual.computeResidual (algebraicAtom left) (algebraicAtom right)
... | Residual.exact = typedComposition left right (operationSuccess left) receipt
... | Residual.partial = typedComposition left right
    (operationResidual Residual.partial "partial typed composition") receipt
... | Residual.noTypedMeet = typedComposition left right
    (operationIncompatibility (namedNoTypedMeet left right receipt)) receipt
... | Residual.contradiction = typedComposition left right
    (operationResidual Residual.contradiction "contradictory composition") receipt

noTypedMeetCompositionEmitsStructuredNamedIncompatibility :
  ∀ left right receipt →
  Residual.computeResidual (algebraicAtom left) (algebraicAtom right)
    ≡ Residual.noTypedMeet →
  result (composeByResidual left right receipt)
    ≡ operationIncompatibility (namedNoTypedMeet left right receipt)
noTypedMeetCompositionEmitsStructuredNamedIncompatibility
  left right receipt residualIsNoTypedMeet
  rewrite residualIsNoTypedMeet = refl

record ScopedNegationReceipt : Set where
  constructor scopedNegationReceipt
  field
    negationSource : EventPNF
    scopeLabel : String
    negatedQualifier : Residual.QualifierState
    negationReceipt : String

open ScopedNegationReceipt public

record ContextProjection : Set where
  constructor contextProjection
  field
    projectionSource : EventPNF
    projectedContext : String
    retainedRoles : List SemanticRole
    projectionResidual : Residual.ResidualLevel
    projectionReceipt : String

open ContextProjection public

------------------------------------------------------------------------
-- Named PNF algebra. These operations preserve witnesses or return explicit
-- residual structure; they do not operate on already-quotiented DomainIRs.
------------------------------------------------------------------------

infixr 4 _⊕_
infixr 5 _⊗_
infixr 6 _∘p_

_⊕_ : CandidatePNF → CandidatePNF → AlternativeFibre
left ⊕ right =
  alternativeFibre (left ∷ right ∷ []) "typed unresolved alternative fibre"

_⊗_ : EventPNF → EventPNF → TypedComposition
left ⊗ right = composeByResidual left right "contextual fibre-product composition"

_∘p_ : EventPNF → EventPNF → TypedComposition
later ∘p earlier = composeByResidual earlier later "temporal/causal PNF composition"

negateScoped : EventPNF → String → ScopedNegationReceipt
negateScoped source scope =
  scopedNegationReceipt source scope Residual.negated "scoped negation receipt"

boundaryPNF : EventPNF → EventPNF → Residual.ResidualLevel
boundaryPNF left right =
  Residual.computeResidual (algebraicAtom left) (algebraicAtom right)

projectToContext :
  EventPNF → String → List SemanticRole → Residual.ResidualLevel → ContextProjection
projectToContext source context roles residual =
  contextProjection source context roles residual "context/chart projection receipt"

revisePNF : EventPNF → EventPNF → RevisionKind → String → PNFRevision
revisePNF before after kind receipt =
  pnfRevision before after kind receipt true refl

invalidIsNotAdmissible : invalid ≡ admissible → ⊥
invalidIsNotAdmissible ()

record PNFProducerBoundary : Set where
  constructor pnfProducerBoundary
  field
    extractorDirectlyPromotesWorldFact : Bool
    extractorDirectlyPromotesWorldFactIsFalse :
      extractorDirectlyPromotesWorldFact ≡ false
    candidateRankingErasesAlternatives : Bool
    candidateRankingErasesAlternativesIsFalse :
      candidateRankingErasesAlternatives ≡ false
    algebraicComparisonIsReceiptBearing : Bool

canonicalPNFProducerBoundary : PNFProducerBoundary
canonicalPNFProducerBoundary =
  pnfProducerBoundary false refl false refl true
