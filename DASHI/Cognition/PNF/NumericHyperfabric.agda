module DASHI.Cognition.PNF.NumericHyperfabric where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.EventAlgebra as ExistingPNF
import DASHI.Interop.SensibLawResidualLattice as Residual
open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.NumericAuthority

------------------------------------------------------------------------
-- Multiscale region DAG.
------------------------------------------------------------------------

data RegionKind : Set where
  sentenceRegion adjacentSentenceRegion paragraphRegion : RegionKind
  adjacentParagraphRegion adaptiveBlockRegion provisionRegion : RegionKind
  sectionRegion chapterRegion executionWindowRegion : RegionKind
  documentRegion trancheRegion : RegionKind

data RegionEdgeKind : Set where
  containsEdge adjacentEdge exportsEdge resolvesEdge supportsEdge : RegionEdgeKind
  continuesEdge executionContainsEdge : RegionEdgeKind

record RegionEdge : Set where
  constructor regionEdge
  field
    sourceRegion targetRegion : RegionId
    edgeKind : RegionEdgeKind
    ordinal : Nat

open RegionEdge public

record TypedAncestors : Set where
  constructor typedAncestors
  field
    nearestParagraph nearestProvision nearestSection nearestChapter : InterfaceId
    nearestExecutionWindow nearestDocument : InterfaceId

open TypedAncestors public

record BinaryLiftAncestor : Set where
  constructor binaryLiftAncestor
  field
    sourceInterface : InterfaceId
    distancePower : Nat
    ancestorInterface : InterfaceId

open BinaryLiftAncestor public

------------------------------------------------------------------------
-- Progressive reduction. The formal carrier does not choose floating-point
-- weights; it proves the promotion gate for whatever natural-number cost model
-- the runtime profile instantiates.
------------------------------------------------------------------------

record PromotionEvidence : Set where
  constructor promotionEvidence
  field
    informationGain representationCost ambiguityCost : Nat
    factorParticipation outwardDemandCount : Nat
    definitionParticipation recurrenceCount : Nat

open PromotionEvidence public

promotionBenefit : PromotionEvidence → Nat
promotionBenefit evidence =
  informationGain evidence
    +ᶜ factorParticipation evidence
    +ᶜ outwardDemandCount evidence
    +ᶜ definitionParticipation evidence
    +ᶜ recurrenceCount evidence

promotionCost : PromotionEvidence → Nat
promotionCost evidence =
  representationCost evidence +ᶜ ambiguityCost evidence

record PromotionWitness (evidence : PromotionEvidence) : Set where
  constructor promotionWitness
  field
    costDoesNotExceedBenefit :
      promotionCost evidence ≤ᶜ promotionBenefit evidence

open PromotionWitness public

data MentionDisposition (evidence : PromotionEvidence) : Set where
  promotedMention : PromotionWitness evidence → MentionDisposition evidence
  retainedInClosedChild : MentionDisposition evidence

------------------------------------------------------------------------
-- Compact interfaces. Descendant graphs are immutable evidence carriers;
-- parents export only promoted keys and unresolved residual demands.
------------------------------------------------------------------------

record ResidualDemandSignature : Set where
  constructor residualDemandSignature
  field
    demandIdentity : DemandId
    demandLookupKey : NumericLookupKey
    residualLevel : Residual.ResidualLevel
    candidateBound : Nat

open ResidualDemandSignature public

record InterfaceSketch : Set where
  constructor interfaceSketch
  field
    sketchInterface : InterfaceId
    uniquePromotedObjectCount : Nat
    uniqueFactorCount : Nat
    unresolvedDemandCount : Nat
    recurrenceCompression : Nat
    dischargedBoundaryPressure : Nat
    interfaceCardinality : Nat
    graphEdgeCount : Nat
    encodedRowCost : Nat
    closureRounds : Nat

open InterfaceSketch public

record ClosedInterface : Set where
  constructor closedInterface
  field
    closedInterfaceId : InterfaceId
    sourceRegion : RegionId
    promotedObjectKeys : List NumericLookupKey
    promotedFactorKeys : List NumericLookupKey
    residualDemands : List ResidualDemandSignature
    sourceCandidatePNFs : List ExistingPNF.CandidatePNF

open ClosedInterface public

data CoverageState : Set where
  openCoverage closedCoverage : CoverageState

data WorldPublication : CoverageState → Set where
  publishClosedResidualInterface :
    ClosedInterface → HumanReference → WorldPublication closedCoverage

openCoverageCannotPublish : WorldPublication openCoverage → ⊥
openCoverageCannotPublish ()

------------------------------------------------------------------------
-- Explicit executor status. The schema may name adjacent scales before the
-- durable overlapping-pair executor exists; those are distinct claims.
------------------------------------------------------------------------

record ReconciliationExecutorStatus : Set where
  constructor reconciliationExecutorStatus
  field
    sentenceExecutorWired : Bool
    adjacentSentenceExecutorWired : Bool
    paragraphExecutorWired : Bool
    adjacentParagraphExecutorWired : Bool
    adaptiveBlockExecutorWired : Bool
    documentExecutorWired : Bool

open ReconciliationExecutorStatus public

currentPR470ExecutorStatus : ReconciliationExecutorStatus
currentPR470ExecutorStatus =
  reconciliationExecutorStatus true false true false true true

record HyperfabricAuthorityBoundary : Set where
  constructor hyperfabricAuthorityBoundary
  field
    unsupportedLocalMentionPromotedAutomatically : Bool
    unsupportedLocalMentionPromotedAutomaticallyIsFalse :
      unsupportedLocalMentionPromotedAutomatically ≡ false
    worldLookupAllowedDuringOpenCoverage : Bool
    worldLookupAllowedDuringOpenCoverageIsFalse :
      worldLookupAllowedDuringOpenCoverage ≡ false
    worldIndexReceivesArbitraryTokens : Bool
    worldIndexReceivesArbitraryTokensIsFalse :
      worldIndexReceivesArbitraryTokens ≡ false
    parentCopiesImmutableChildGraphs : Bool
    parentCopiesImmutableChildGraphsIsFalse :
      parentCopiesImmutableChildGraphs ≡ false

canonicalHyperfabricAuthorityBoundary : HyperfabricAuthorityBoundary
canonicalHyperfabricAuthorityBoundary =
  hyperfabricAuthorityBoundary false refl false refl false refl false refl
