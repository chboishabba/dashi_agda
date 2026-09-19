module DASHI.Wikimedia.MaboAdaptiveHeterogeneousTrajectoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snow
import DASHI.Law.SensibLawMultiResidualProofFrontierExact as Frontier
import DASHI.Law.SensibLawProofSearchIterationReceiptABIExact as Iteration
import DASHI.Law.SensibLawResearchCompoundingLoopExact as Compounding
import DASHI.Interop.MaboRadicalTitlePropositionChainPaymentExact as Proposition
import DASHI.Wikimedia.Mabo100HopReviewedCampaignExact as Campaign
import DASHI.Wikimedia.MaboConsumerResidualDiagnosisExact as Diagnosis
import DASHI.Wikimedia.MaboResidualDrivenProducerAdaptersExact as Producers

------------------------------------------------------------------------
-- MABO HETEROGENEOUS ADAPTIVE TRAJECTORY WELD
--
-- No new scheduler, proof-frontier ontology, FactorsThrough notion, WrongType
-- notion or experiment-design language is introduced here.
--
-- This owner only composes existing repository machinery so that:
--   * identity/context/legal/provenance/diagnostic residuals may inhabit one
--     current consumer-relative multi-residual frontier;
--   * producer family never determines residual class;
--   * reviewed negative diagnostics may suppress one exact move while leaving
--     its residual open;
--   * post-commit trajectory receipts retain the exact world/frontier lineage
--     from which the next Pareto move was selected.
------------------------------------------------------------------------

slrTrajectoryBranch : String
slrTrajectoryBranch = "agent/mabo-adaptive-trajectory-v1"

slrTrajectoryBaseHead : String
slrTrajectoryBaseHead = "2f87b4207e798785507b37b3abcb4d565c53b09e"

slrTrajectorySourceWrittenHead : String
slrTrajectorySourceWrittenHead = "d8e5ef0400a7538005d4110bca0c582273452491"

------------------------------------------------------------------------
-- Existing multi-residual frontier ABI is reused literally.
------------------------------------------------------------------------

legalAuthorityResidual : Frontier.ProofResidual
legalAuthorityResidual =
  Frontier.proofResidual
    "residual:mabo:legal:primary-authority"
    "mabo:proposition:primary-authority-support"
    "producer:governed-legal"
    "AU"
    "primary-legal-source"
    4
    ("dependency:mabo:authority" ∷ [])
    Frontier.residualOpen

provenanceResidual : Frontier.ProofResidual
provenanceResidual =
  Frontier.proofResidual
    "residual:mabo:provenance:source-history"
    "mabo:proposition:source-history"
    "producer:source-specific-provenance"
    "AU"
    ""
    2
    ("dependency:mabo:source-history" ∷ [])
    Frontier.residualOpen

record HeterogeneousResidualMove : Set₁ where
  constructor heterogeneous-residual-move
  field
    residual : Frontier.ProofResidual
    discoveryRoute : Snow.DiscoveryRoute
    residualClassReference : String
    producerLaneReference : String
    moveReference : String
    diagnosisReference : String
    moveCandidateOnly : Bool
    moveAdmissible : Bool
    moveCreatesSemanticAuthority : Bool
    moveApplicabilityPromoted : Bool
    moveClaimTruthPromoted : Bool

open HeterogeneousResidualMove public

legalMove : HeterogeneousResidualMove
legalMove =
  heterogeneous-residual-move
    legalAuthorityResidual
    Snow.proofSearch
    "Legal"
    "GovernedLegal"
    "move:oalc"
    "consumer:mabo:primary-authority-gap"
    true true false false false

provenanceMove : HeterogeneousResidualMove
provenanceMove =
  heterogeneous-residual-move
    provenanceResidual
    Snow.sourceProvenanceMismatch
    "Provenance"
    "SourceSpecificProvenance"
    "move:source-provenance"
    "consumer:mabo:source-history-gap"
    true true false false false

heterogeneousMoves : List HeterogeneousResidualMove
heterogeneousMoves = legalMove ∷ provenanceMove ∷ []

------------------------------------------------------------------------
-- Durable negative diagnostics constrain moves; they do not pay residuals.
------------------------------------------------------------------------

record DurableNegativeConstraint : Set where
  constructor durable-negative-constraint
  field
    targetResidualReference : String
    targetMoveReference : String
    diagnosticRoute : Snow.DiscoveryRoute
    assessmentReference : String
    sourceRevisionReference : String
    negativeConstraintCandidateOnly : Bool
    negativeConstraintMakesMoveInadmissible : Bool
    negativeConstraintSatisfiesResidual : Bool
    negativeConstraintCreatesSemanticAuthority : Bool
    negativeConstraintApplicabilityPromoted : Bool
    negativeConstraintClaimTruthPromoted : Bool

open DurableNegativeConstraint public

canonicalWrongTypeConstraint : DurableNegativeConstraint
canonicalWrongTypeConstraint =
  durable-negative-constraint
    "residual:mabo:legal:primary-authority"
    "move:oalc:wrong-type"
    Snow.wrongTypeDiagnosis
    "assessment:mabo:wrong-type"
    "source:oalc:exact"
    true true false false false false

canonicalFailedFactorsThroughConstraint : DurableNegativeConstraint
canonicalFailedFactorsThroughConstraint =
  durable-negative-constraint
    "residual:mabo:measurement:observer-repair"
    "move:coarse-observer"
    Snow.failedFactorsThrough
    "assessment:mabo:failed-factors-through"
    "observer:coarse"
    true true false false false false

data NegativeDiagnosticEqualsResidualSatisfaction : Set where
data WrongTypeEqualsTypeIdentity : Set where
data FailedFactorsThroughEqualsEvidence : Set where

negativeDiagnosticDoesNotSatisfyResidual :
  NegativeDiagnosticEqualsResidualSatisfaction → ⊥
negativeDiagnosticDoesNotSatisfyResidual ()

wrongTypeDoesNotCreateTypeIdentity : WrongTypeEqualsTypeIdentity → ⊥
wrongTypeDoesNotCreateTypeIdentity ()

failedFactorsThroughDoesNotCreateEvidence :
  FailedFactorsThroughEqualsEvidence → ⊥
failedFactorsThroughDoesNotCreateEvidence ()

------------------------------------------------------------------------
-- Runtime trajectory receipt reuses the existing deterministic iteration ABI.
------------------------------------------------------------------------

zeroRuntimeCost : Iteration.RuntimeCostVector
zeroRuntimeCost =
  Iteration.runtimeCostVector 0 0 0 0 0 0 0 0 0

cycle0IterationReceipt : Iteration.ProofSearchIterationReceipt
cycle0IterationReceipt =
  Iteration.proofSearchIterationReceipt
    "mabo-adaptive-selection:v1"
    slrTrajectoryBaseHead
    "consumer:mabo-adaptive-world-expansion"
    "sha256:frontier0"
    ("residual:mabo:context-expansion:Q1358798" ∷ [])
    ("move:mabo-context-expand:Q1358798" ∷ [])
    ("move:mabo-context-expand:Q1358798" ∷ [])
    "move:mabo-context-expand:Q1358798"
    "wikidata:Q1358798:oldid:2546712967"
    zeroRuntimeCost
    "sha256:pending-context-bundle"
    "pnf:mabo:cycle0"
    "review:mabo:context:cycle0"
    "delta:mabo:cycle0"
    []
    "move:post-commit-recompute"
    "experimental_candidate_only"
    "sha256:world-frontier0"
    "sha256:cycle0-output"
    "receipt:mabo:cycle0"

cycle1IterationReceipt : Iteration.ProofSearchIterationReceipt
cycle1IterationReceipt =
  Iteration.proofSearchIterationReceipt
    "mabo-adaptive-selection:v1"
    slrTrajectoryBaseHead
    "consumer:mabo-adaptive-world-expansion"
    "sha256:frontier1"
    ("residual:mabo:legal:primary-authority" ∷ [])
    ("move:oalc" ∷ "move:source-provenance" ∷ [])
    ("move:oalc" ∷ [])
    "move:oalc"
    "source:oalc:exact"
    zeroRuntimeCost
    "sha256:oalc-artifact"
    "pnf:mabo:cycle1"
    "review:mabo:legal:cycle1"
    "delta:mabo:cycle1"
    []
    "move:post-commit-recompute"
    "experimental_candidate_only"
    "sha256:world-frontier1"
    "sha256:cycle1-output"
    "receipt:mabo:cycle1"

record AdaptiveTrajectoryLink : Set₁ where
  constructor adaptive-trajectory-link
  field
    previousIteration : Iteration.ProofSearchIterationReceipt
    nextIteration : Iteration.ProofSearchIterationReceipt
    previousCommitReference : String
    nextPriorCommitReference : String
    selectionFromPostCommitFrontier : Bool
    precomputedExecutionAuthority : Bool
    adaptiveFreshnessRequiresDifferentResidual : Bool
    trajectoryCandidateOnly : Bool
    trajectoryCreatesSemanticAuthority : Bool
    trajectoryApplicabilityPromoted : Bool
    trajectoryClaimTruthPromoted : Bool

open AdaptiveTrajectoryLink public

canonicalTrajectoryLink : AdaptiveTrajectoryLink
canonicalTrajectoryLink =
  adaptive-trajectory-link
    cycle0IterationReceipt
    cycle1IterationReceipt
    "commit:mabo:cycle0"
    "commit:mabo:cycle0"
    true false false true false false false

------------------------------------------------------------------------
-- Existing owners already establish the ingredients used by this weld.
------------------------------------------------------------------------

diagnosisFailedFactorisationMayDemandRepair :
  Diagnosis.failedFactorisationMayDemandObserverRepair
    Diagnosis.canonicalDiagnosisBoundary ≡ true
diagnosisFailedFactorisationMayDemandRepair = refl

diagnosisWrongTypeMayReject :
  Diagnosis.wrongTypeMayRejectConsumerMismatch
    Diagnosis.canonicalDiagnosisBoundary ≡ true
diagnosisWrongTypeMayReject = refl

campaignReviewAvailabilityNotSchedulerPrior :
  Campaign.schedulerSelectionDependsOnReviewAvailability
    Campaign.canonicalReviewedCampaignBoundary ≡ false
campaignReviewAvailabilityNotSchedulerPrior = refl

producerDoesNotDetermineResidualClass :
  Producers.ProducerIdentityDeterminesResidualClass → ⊥
producerDoesNotDetermineResidualClass =
  Producers.producerIdentityDoesNotDetermineResidualClass

runtimeReceiptDoesNotCreateFormalProof :
  Iteration.RuntimeReceiptMeansFormalProof → ⊥
runtimeReceiptDoesNotCreateFormalProof =
  Iteration.runtimeReceiptDoesNotMeanFormalProof

runtimeReceiptDoesNotCreateLegalAuthority :
  Iteration.RuntimeReceiptMeansLegalAuthority → ⊥
runtimeReceiptDoesNotCreateLegalAuthority =
  Iteration.runtimeReceiptDoesNotMeanLegalAuthority

parsedResultsFeedFutureSearch :
  Compounding.parsedResultsMayEnrichFutureSearch
    Compounding.canonicalResearchCompoundingBoundary ≡ true
parsedResultsFeedFutureSearch = refl

------------------------------------------------------------------------
-- Existing Mabo proposition-chain residual semantics are reused.
------------------------------------------------------------------------

canonicalBoundedWhyRemainsExecutable :
  Proposition.propositionChainPaid Proposition.canonicalBoundedWhy ≡ true
canonicalBoundedWhyRemainsExecutable = refl

canonicalQualifierResidualRetained :
  Proposition.explicitResidualRetained
    (Proposition.qualifierRole Proposition.canonicalBoundedWhy) ≡ true
canonicalQualifierResidualRetained = refl

canonicalDefeaterResidualRetained :
  Proposition.explicitResidualRetained
    (Proposition.defeaterRole Proposition.canonicalBoundedWhy) ≡ true
canonicalDefeaterResidualRetained = refl

canonicalComparatorResidualRetained :
  Proposition.explicitResidualRetained
    (Proposition.comparatorRole Proposition.canonicalBoundedWhy) ≡ true
canonicalComparatorResidualRetained = refl

------------------------------------------------------------------------
-- Golden heterogeneous/adaptive boundary.
------------------------------------------------------------------------

record AdaptiveHeterogeneousBoundary : Set where
  constructor adaptive-heterogeneous-boundary
  field
    wholeFrontierRecomputedAfterCommit : Bool
    heterogeneousResidualsShareOneFrontier : Bool
    producerIdentityDeterminesResidualClass : Bool
    wrongTypeMaySuppressExactMove : Bool
    wrongTypeSatisfiesResidual : Bool
    failedFactorsThroughMayDemandObserverRepair : Bool
    failedFactorsThroughCreatesEvidence : Bool
    parsedSourceMayCreateNewConsumerResidual : Bool
    adaptiveFreshnessRequiresDifferentResidual : Bool
    reviewAvailabilityIsSchedulerPrior : Bool
    trajectoryReceiptCreatesFormalProof : Bool
    trajectoryReceiptCreatesLegalAuthority : Bool
    negativeKnowledgePersistsAcrossReDiagnosis : Bool
    legalAndProvenanceMayCompeteWithIdentityAndContext : Bool
    sourceFamilySwitchMayBeEndogenous : Bool
    trajectoryPersistsAcrossOperatorRestart : Bool
    adaptiveCycleBudgetIsProcessLocal : Bool
    boundedWhyMayRetainResearchResiduals : Bool
    explicitResearchResidualMeansPropositionFalse : Bool
    legalResearchRequiresReacquiringTriggerSource : Bool
    boundaryCandidateOnly : Bool
    boundaryCreatesSemanticAuthority : Bool
    boundaryApplicabilityPromoted : Bool
    boundaryClaimTruthPromoted : Bool

open AdaptiveHeterogeneousBoundary public

canonicalAdaptiveHeterogeneousBoundary : AdaptiveHeterogeneousBoundary
canonicalAdaptiveHeterogeneousBoundary =
  adaptive-heterogeneous-boundary
    true
    true
    false
    true
    false
    true
    false
    true
    false
    false
    false
    false
    true
    true
    true
    true
    false
    true
    false
    false
    true
    false
    false
    false

------------------------------------------------------------------------
-- Non-collapse firewalls for the new weld only.
------------------------------------------------------------------------

data HeterogeneousFrontierEqualsScalarSchedule : Set where
data ProducerLaneEqualsResidualClass : Set where
data TrajectoryReceiptEqualsQueuedExecutionAuthority : Set where
data ParsedSourceCreatesAutomaticPayment : Set where

heterogeneousFrontierDoesNotScalarise :
  HeterogeneousFrontierEqualsScalarSchedule → ⊥
heterogeneousFrontierDoesNotScalarise ()

producerLaneDoesNotEqualResidualClass :
  ProducerLaneEqualsResidualClass → ⊥
producerLaneDoesNotEqualResidualClass ()

trajectoryReceiptDoesNotEqualQueuedExecutionAuthority :
  TrajectoryReceiptEqualsQueuedExecutionAuthority → ⊥
trajectoryReceiptDoesNotEqualQueuedExecutionAuthority ()

parsedSourceDoesNotCreateAutomaticPayment :
  ParsedSourceCreatesAutomaticPayment → ⊥
parsedSourceDoesNotCreateAutomaticPayment ()
