module DASHI.Interop.SLRClaimFragmentResidualInheritanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRClaimFragmentProjectionExact as Fragment
import DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact as C029
import DASHI.Policy.ABC730C029EvidenceRoadmapExact as Roadmap

------------------------------------------------------------------------
-- CLAIM-LOCAL FRAGMENT RESIDUAL INHERITANCE
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_claim_fragment_residual_inheritance.py
--   schema = slr-claim-fragment-residual-inheritance-v1
--
-- A local fragment may inherit the canonical claim's downstream consumer /
-- evidence obligations.  Inheritance does not pay whole-claim extent, does
-- not assign neighbouring claims to intermediate fragments, and does not
-- promote the canonical proposition to truth.
------------------------------------------------------------------------

data ResidualStatus : Set where
  residualOpen : ResidualStatus
  residualBlockedByMeasurement : ResidualStatus
  residualDownstream : ResidualStatus
  residualPaid : ResidualStatus

record CanonicalClaimObligation : Set where
  constructor canonicalClaimObligation
  field
    claimReference : String
    obligationReference : String
    status : ResidualStatus
    ownerReference : String
    paymentReference : String
    evidenceKindRequired : String

open CanonicalClaimObligation public

record FragmentResidualInheritance : Set where
  constructor fragmentResidualInheritance
  field
    fragmentReference : String
    canonicalClaimReference : String
    inheritedObligations : List CanonicalClaimObligation
    wholeClaimExtentPaid : Bool
    claimTruthPromoted : Bool
    intermediateAdjacencyUsedToAssignClaim : Bool
    appendOnly : Bool
    candidateOnly : Bool

open FragmentResidualInheritance public

c029SettlementClassifier : CanonicalClaimObligation
c029SettlementClassifier = canonicalClaimObligation
  "ABC730-2026-09-09-C029"
  "settlementSubcountryClassifier"
  residualOpen
  "DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact"
  "settlement-place legal test + production-location evidence + declaration/application semantics"
  "application/classifier evidence"

c029AdviceLineage : CanonicalClaimObligation
c029AdviceLineage = canonicalClaimObligation
  "ABC730-2026-09-09-C029"
  "adviceDecisionLineage"
  residualOpen
  "DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact"
  "same-object departmental analysis -> ministerial brief -> public rationale -> policy decision lineage"
  "Atom lineage receipt"

c029PalestinianIncidence : CanonicalClaimObligation
c029PalestinianIncidence = canonicalClaimObligation
  "ABC730-2026-09-09-C029"
  "palestinianNetIncidence"
  residualOpen
  "DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact"
  "situated worker/reallocation/substitution/household-income counterfactual"
  "situated incidence evidence"

c029Counterfactual : CanonicalClaimObligation
c029Counterfactual = canonicalClaimObligation
  "ABC730-2026-09-09-C029"
  "targetedVsBlanketCounterfactual"
  residualOpen
  "DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact"
  "consumer-adequate comparison of incremental compliance cost, coverage, evasion, substitution and expected effect"
  "comparative instrument evidence"

c029ObligationSurface : List CanonicalClaimObligation
c029ObligationSurface =
  c029SettlementClassifier ∷
  c029AdviceLineage ∷
  c029PalestinianIncidence ∷
  c029Counterfactual ∷ []

wongC029ResidualInheritance : FragmentResidualInheritance
wongC029ResidualInheritance = fragmentResidualInheritance
  "spaCy-42:segment-0"
  "ABC730-2026-09-09-C029"
  c029ObligationSurface
  false false false true true

record IntermediateFragmentResidualBoundary : Set where
  constructor intermediateFragmentResidualBoundary
  field
    fragmentReference : String
    canonicalClaimAssigned : Bool
    neighbouringClaimDebtInherited : Bool
    retained : Bool
    candidateOnly : Bool

open IntermediateFragmentResidualBoundary public

greberResidualBoundary : IntermediateFragmentResidualBoundary
greberResidualBoundary = intermediateFragmentResidualBoundary
  "spaCy-42:segment-1"
  false false true true

------------------------------------------------------------------------
-- Contraction law.
--
-- Later Snowball evidence may replace/open->paid obligation state in a later
-- append-only receipt, but it cannot rewrite the earlier fragment/source state.
------------------------------------------------------------------------

record ResidualContractionReceipt : Set where
  constructor residualContractionReceipt
  field
    priorObligationReference : String
    laterPaymentReceiptReference : String
    priorStateRetained : Bool
    laterStateAppended : Bool
    sourceFragmentRewritten : Bool
    claimTruthCreatedByContraction : Bool

open ResidualContractionReceipt public

canonicalResidualContractionBoundary : ResidualContractionReceipt
canonicalResidualContractionBoundary = residualContractionReceipt
  "canonical claim obligation"
  "later Ibrahim/Snowball evidence receipt"
  true true false false

------------------------------------------------------------------------
-- Runtime boundary.
------------------------------------------------------------------------

record FragmentResidualRuntimeBoundary : Set where
  constructor fragmentResidualRuntimeBoundary
  field
    schemaReference : String
    explicitClaimResidualMapRequired : Bool
    adjacencyMayAssignNeighbourClaimDebt : Bool
    claimLocalFragmentMayInheritCanonicalConsumerDebt : Bool
    inheritancePaysWholeClaimExtent : Bool
    inheritancePromotesClaimTruth : Bool
    baseFragmentWorldRewritten : Bool
    appendOnly : Bool
    candidateOnly : Bool

open FragmentResidualRuntimeBoundary public

canonicalFragmentResidualRuntimeBoundary : FragmentResidualRuntimeBoundary
canonicalFragmentResidualRuntimeBoundary = fragmentResidualRuntimeBoundary
  "slr-claim-fragment-residual-inheritance-v1"
  true false true false false false true true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FragmentDebtMeansFragmentFalse : Set where
data InheritedDebtPaysWholeClaimExtent : Set where
data IntermediateAdjacencyMayAssignClaimDebt : Set where
data ResidualPaymentMayRewriteHistoricalFragment : Set where
data ResidualContractionPromotesTruth : Set where

fragmentDebtDoesNotMeanFragmentFalse : FragmentDebtMeansFragmentFalse → ⊥
fragmentDebtDoesNotMeanFragmentFalse ()

inheritedDebtDoesNotPayWholeClaim : InheritedDebtPaysWholeClaimExtent → ⊥
inheritedDebtDoesNotPayWholeClaim ()

intermediateAdjacencyMayNotAssignClaimDebt : IntermediateAdjacencyMayAssignClaimDebt → ⊥
intermediateAdjacencyMayNotAssignClaimDebt ()

paymentMayNotRewriteHistoricalFragment : ResidualPaymentMayRewriteHistoricalFragment → ⊥
paymentMayNotRewriteHistoricalFragment ()

contractionDoesNotPromoteTruth : ResidualContractionPromotesTruth → ⊥
contractionDoesNotPromoteTruth ()

------------------------------------------------------------------------
-- Existing-owner anchors.
------------------------------------------------------------------------

fragmentBoundaryAnchor : Fragment.ClaimFragmentProjectionBoundary
fragmentBoundaryAnchor = Fragment.canonicalClaimFragmentProjectionBoundary

c029CutsetAnchor : C029.C029LegalEvidenceCutset
c029CutsetAnchor = C029.canonicalC029Cutset

c029RoadmapAnchor : Roadmap.C029RoadmapSummary
c029RoadmapAnchor = Roadmap.canonicalC029RoadmapSummary
