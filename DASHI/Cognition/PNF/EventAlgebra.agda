module DASHI.Cognition.PNF.EventAlgebra where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Cognition.Utterance.LayeredMeaningCore as Utterance
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- PNF sits between extractor observations and task-specific operational IR.
-- Extractors may propose candidates heuristically; all PNF objects remain
-- span/provenance-bearing and all algebraic comparison is explicit.
------------------------------------------------------------------------

data ParserProducer : Set where
  spaCyProducer stanzaProducer asrProducer ruleProducer : ParserProducer
  udProducer uccaProducer mrsProducer amrProducer specialistProducer : ParserProducer

data CandidateValidity : Set where
  admissible invalid undetermined inapplicable : CandidateValidity

data SemanticRole : Set where
  actorRole actionRole objectRole modalityRole conditionRole : SemanticRole
  exceptionRole qualifierRole jurisdictionRole speakerRole : SemanticRole
  evidenceRole temporalRole provenanceRole unknownRole : SemanticRole

data RevisionKind : Set where
  parserCorrection entityResolutionCorrection translationRevision : RevisionKind
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
  equivalent compatible contradictory residuallyDifferent noTypedMeet : ComparisonResult

comparisonFromResidual : Residual.ResidualLevel → ComparisonResult
comparisonFromResidual Residual.exact = equivalent
comparisonFromResidual Residual.partial = residuallyDifferent
comparisonFromResidual Residual.noTypedMeet = noTypedMeet
comparisonFromResidual Residual.contradiction = contradictory

comparePNF : EventPNF → EventPNF → ComparisonResult
comparePNF left right =
  comparisonFromResidual
    (Residual.computeResidual (algebraicAtom left) (algebraicAtom right))

data PNFOperationResult : Set where
  operationSuccess : EventPNF → PNFOperationResult
  operationResidual : Residual.ResidualLevel → String → PNFOperationResult
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
    (operationResidual Residual.noTypedMeet "NO_TYPED_MEET") receipt
... | Residual.contradiction = typedComposition left right
    (operationResidual Residual.contradiction "contradictory composition") receipt

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
