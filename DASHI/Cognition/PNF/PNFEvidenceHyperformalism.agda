module DASHI.Cognition.PNF.PNFEvidenceHyperformalism where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.PossibilityAccessibilitySupport as Axes
import DASHI.Core.ProvenanceBearingQuotient as Quotient
import DASHI.Core.ConsumerIndexedRelevanceMeasure as Relevance
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Analysis.NormalizedFibreAveragingExact as Averaging
import DASHI.Analysis.GlassesProjectionInvolutionExact as Glasses
import DASHI.Reasoning.RelationalTernaryPhaseGeometry as Phase
import DASHI.Reasoning.RelationalBranchInterference as Interference
import DASHI.Biology.TraumaPsychogeographicMetricExact as TraumaMetric
import DASHI.Biology.ReachableSectorEntropyExact as ReachabilityReference

import DASHI.Cognition.PNF.ReopenableEvidenceFibre as Reopenable
import DASHI.Cognition.PNF.EvidenceHorizon369 as Horizon

------------------------------------------------------------------------
-- PNF compatibility name for the canonical independent candidate axes.
------------------------------------------------------------------------

EvidenceAccessibility : Set → Set₁
EvidenceAccessibility = Axes.PossibilityAccessibilitySupport

open Axes.PossibilityAccessibilitySupport public

record AccessibilityDeformation (Candidate : Set) : Set where
  constructor accessibilityDeformation
  field
    beforeCost : Candidate → Nat
    afterCost : Candidate → Nat
    historyReceipt : String

open AccessibilityDeformation public

------------------------------------------------------------------------
-- Assembly of existing DASHI cores, not a parallel hypergraph/ternary/PQJ
-- implementation.
------------------------------------------------------------------------

record PNFEvidenceHyperformalism
    (Vertex Edge Candidate : Set) : Set₁ where
  constructor pnfEvidenceHyperformalism
  field
    fabric : Hyperfabric.TypedHyperfabric Vertex Edge
    fibreCore : Fibre.FibreRestrictionCore
    reopening : Reopenable.ReopenableFibreExtension fibreCore
    accessibility : EvidenceAccessibility Candidate
    localStructuralH3 : Horizon.H3Evidence Candidate
    discourseTemporalH6 : Horizon.H6Evidence Candidate
    externalAuthorityH9 : Horizon.H9Evidence Candidate

open PNFEvidenceHyperformalism public

------------------------------------------------------------------------
-- Optional consumer-indexed relevance accounting.
--
-- This wrapper does not reinterpret the base hyperformalism as a probability
-- space.  A caller chooses candidate-weight, represented-provenance, or
-- consumer/task relevance semantics explicitly through the measure's massKind.
------------------------------------------------------------------------

record MeasuredPNFEvidenceHyperformalism
    (Vertex Edge Candidate Consumer Region Mass : Set) : Set₁ where
  constructor measuredPNFEvidenceHyperformalism
  field
    baseHyperformalism : PNFEvidenceHyperformalism Vertex Edge Candidate
    relevanceMeasure :
      Relevance.ConsumerIndexedRelevanceMeasure Consumer Region Mass
    consumer : Consumer
    relevanceAccounting :
      Relevance.OpenWorldMassAccounting relevanceMeasure consumer

open MeasuredPNFEvidenceHyperformalism public

module ComplementaryReadingReference {Candidate : Set} =
  Glasses.GlassesSystem {Base = Candidate}

record ExistingReferenceSpine : Set where
  constructor existingReferenceSpine
  field
    finiteNormalisedFibreBoundary : Averaging.NormalizedFibreClaimScope
    finitePQJBoundary : Glasses.GlassesInvolutionClaimScope
    ternaryPhaseBoundary : Phase.TernaryPhaseAuthorityBoundary
    branchInterferenceBoundary : Interference.BranchInterferenceAuthorityBoundary
    typedHyperfabricBoundary : Hyperfabric.TypedHyperfabricAuthorityBoundary
    pathAccessibilityBoundary : TraumaMetric.TraumaPsychogeographicBoundary
    reachableSectorBoundary : ReachabilityReference.ReachableSectorBoundary
    provenanceQuotientBoundary : Quotient.ProvenanceBearingQuotientBoundary
    consumerRelevanceBoundary : Relevance.ConsumerIndexedRelevanceBoundary

open ExistingReferenceSpine public

canonicalExistingReferenceSpine : ExistingReferenceSpine
canonicalExistingReferenceSpine =
  existingReferenceSpine
    Averaging.canonicalNormalizedFibreClaimScope
    Glasses.canonicalGlassesInvolutionClaimScope
    Phase.canonicalTernaryPhaseAuthorityBoundary
    Interference.canonicalBranchInterferenceAuthorityBoundary
    Hyperfabric.canonicalTypedHyperfabricAuthorityBoundary
    TraumaMetric.canonicalTraumaPsychogeographicBoundary
    ReachabilityReference.canonicalReachableSectorBoundary
    Quotient.canonicalProvenanceBearingQuotientBoundary
    Relevance.canonicalConsumerIndexedRelevanceBoundary

data UniversalSemanticPQJPermission : Set where

finiteReferenceDoesNotPromoteUniversalPQJ :
  UniversalSemanticPQJPermission → ⊥
finiteReferenceDoesNotPromoteUniversalPQJ ()

record PNFEvidenceHyperformalismBoundary : Set where
  constructor pnfEvidenceHyperformalismBoundary
  field
    hypergraphCoreDuplicated : Bool
    hypergraphCoreDuplicatedIsFalse : hypergraphCoreDuplicated ≡ false
    ternaryPhaseCoreDuplicated : Bool
    ternaryPhaseCoreDuplicatedIsFalse : ternaryPhaseCoreDuplicated ≡ false
    finitePQJPromotedUniversally : Bool
    finitePQJPromotedUniversallyIsFalse : finitePQJPromotedUniversally ≡ false
    accessibilityEqualsSemanticPossibility : Bool
    accessibilityEqualsSemanticPossibilityIsFalse :
      accessibilityEqualsSemanticPossibility ≡ false
    reopenableQuotientCoreDuplicated : Bool
    reopenableQuotientCoreDuplicatedIsFalse :
      reopenableQuotientCoreDuplicated ≡ false
    normalizedRelevanceMassEqualsWorldTruth : Bool
    normalizedRelevanceMassEqualsWorldTruthIsFalse :
      normalizedRelevanceMassEqualsWorldTruth ≡ false

open PNFEvidenceHyperformalismBoundary public

canonicalPNFEvidenceHyperformalismBoundary : PNFEvidenceHyperformalismBoundary
canonicalPNFEvidenceHyperformalismBoundary =
  pnfEvidenceHyperformalismBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
