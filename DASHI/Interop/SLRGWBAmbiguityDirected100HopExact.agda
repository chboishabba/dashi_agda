module DASHI.Interop.SLRGWBAmbiguityDirected100HopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRGWBExecutionRoadmapExact as Roadmap
import DASHI.Interop.SLRGWBCandidateWorldProjectionExact as Carrier
import DASHI.Interop.SLRWorldResearchIterationBudgetExact as Budget
import DASHI.Interop.SLRWikimediaFirstWorldAcquisitionExact as Wikimedia
import DASHI.Interop.SLRExternalOntologyEnrichmentRouterExact as External
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Core.ExperimentalCoordinateDesignExact as Experiment
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as LeastPrivilege
import DASHI.Interop.GodsEyeViewHighestAlphaObservationChoiceExact as HighestAlpha
import DASHI.Interop.GodsEyeViewExecutableWorldResearchLoopExact as ReturnLoop
import DASHI.Interop.GodsEyeViewAcquisitionResultAssessmentBridgeExact as Assessment
import DASHI.Interop.GodsEyeViewWorldResearchFrontierActionExact as FrontierAction

------------------------------------------------------------------------
-- GEORGE-W.-BUSH GWB AMBIGUITY-DIRECTED 100-HOP CAMPAIGN
--
-- "GWB" in this module is the existing George W. Bush tranche, not the
-- GodsEyeView namespace imported above as generic world-research machinery.
--
-- Runtime owner:
--   chboishabba/slr
--   branch agent/gwb-ambiguity-100hop-v1
--   verified runtime head 9ef5d562a510d4a9cb861d66016d28d84eaa8ddd
--
-- SensibLaw reference:
--   chboishabba/SensibLaw
--   d25cddf73540bdbb313777bbf566280f4e34313b
--   docs/external_graph_bridge.md
--
-- The tranche does not introduce a new world model, Pareto order, proof-search
-- scheduler, review ontology, or Snowball policy. It welds the already-paid GWB
-- CandidateWorldModel/world-research surface to the existing non-scalar
-- observation-choice and executable return loop.
------------------------------------------------------------------------

slrSourceWrittenHead : String
slrSourceWrittenHead = "9ef5d562a510d4a9cb861d66016d28d84eaa8ddd"

sensibLawReferenceHead : String
sensibLawReferenceHead = "d25cddf73540bdbb313777bbf566280f4e34313b"

data GWBAmbiguityAxis : Set where
  identityAxis : GWBAmbiguityAxis
  sourceWorkIdentityAxis : GWBAmbiguityAxis
  typeClassAxis : GWBAmbiguityAxis
  superclassAxis : GWBAmbiguityAxis
  subclassAxis : GWBAmbiguityAxis
  propertySupportAxis : GWBAmbiguityAxis
  crossLanguageGapAxis : GWBAmbiguityAxis
  unsupportedDependencyAxis : GWBAmbiguityAxis
  provenanceAxis : GWBAmbiguityAxis
  competingAlternativesAxis : GWBAmbiguityAxis
  consumerSemanticGapAxis : GWBAmbiguityAxis

data GWBInvestigationKind : Set where
  inspectIdentity : GWBInvestigationKind
  inspectTypeClass : GWBInvestigationKind
  inspectSuperclass : GWBInvestigationKind
  queryInverseSubclass : GWBInvestigationKind
  inspectProperty : GWBInvestigationKind
  inspectWikipediaSurface : GWBInvestigationKind
  inspectSource : GWBInvestigationKind
  inspectProvenance : GWBInvestigationKind
  repairParser : GWBInvestigationKind
  consultExternalOntology : GWBInvestigationKind
  broadenSnowball : GWBInvestigationKind

record GWBAmbiguityResidualShape : Set where
  constructor gwb-ambiguity-residual-shape
  field
    residualReference : String
    subjectReference : String
    ambiguityAxis : GWBAmbiguityAxis
    consumerReference : String
    rootQidReference : String
    salienceReference : String
    dependencyReference : String
    candidateResidualOnly : Bool
    residualCreatesTruth : Bool

open GWBAmbiguityResidualShape public

canonicalTypeResidual : GWBAmbiguityResidualShape
canonicalTypeResidual =
  gwb-ambiguity-residual-shape
    "residual:gwb:Q207:type-class"
    "Q207"
    typeClassAxis
    "consumer:gwb-ambiguity-directed-world-research"
    "Q207"
    "consumer-relative ambiguity salience"
    "existing GWB world/source-role dependency"
    true
    false

------------------------------------------------------------------------
-- Non-scalar experimental coordinates.
------------------------------------------------------------------------

record GWBParetoCoordinatePolicy : Set where
  constructor gwb-pareto-coordinate-policy
  field
    residualContractionSeparate : Bool
    ambiguityReductionSeparate : Bool
    typeClosureGainSeparate : Bool
    crossSurfaceGapGainSeparate : Bool
    sourceSupportGainSeparate : Bool
    sharedDependencyGainSeparate : Bool
    acquisitionCostSeparate : Bool
    universalScalarAmbiguityScoreRequired : Bool
    qidLexicalOrderIsEpistemicPriority : Bool
    frontierRankCreatesTruth : Bool

open GWBParetoCoordinatePolicy public

canonicalGWBParetoCoordinatePolicy : GWBParetoCoordinatePolicy
canonicalGWBParetoCoordinatePolicy =
  gwb-pareto-coordinate-policy
    true true true true true true true
    false false false

record GWBClassDisambiguationPolicy : Set where
  constructor gwb-class-disambiguation-policy
  field
    similarityAloneMayMergeClasses : Bool
    reviewedSharedSuperclassMayBeRetained : Bool
    reviewedBridgeClassMayBeRetained : Bool
    reviewedConditionalDistinctionMayBeRetained : Bool
    externalClassCreatesInternalOntologyTruth : Bool
    classReviewCreatesLegalNormativity : Bool

open GWBClassDisambiguationPolicy public

canonicalGWBClassDisambiguationPolicy : GWBClassDisambiguationPolicy
canonicalGWBClassDisambiguationPolicy =
  gwb-class-disambiguation-policy
    false true true true false false

------------------------------------------------------------------------
-- One reviewed hop.
------------------------------------------------------------------------

data GWBReviewOutcome : Set where
  resolvedOutcome : GWBReviewOutcome
  sameObjectOutcome : GWBReviewOutcome
  newRelatedObjectOutcome : GWBReviewOutcome
  newConceptualParentOutcome : GWBReviewOutcome
  sharedSuperclassOutcome : GWBReviewOutcome
  bridgeClassOutcome : GWBReviewOutcome
  conditionalDistinctionOutcome : GWBReviewOutcome
  newEvidentiarySourceOutcome : GWBReviewOutcome
  wrongTypeOutcome : GWBReviewOutcome
  duplicateOutcome : GWBReviewOutcome
  irrelevantOutcome : GWBReviewOutcome
  emptyOutcome : GWBReviewOutcome
  noSupportOutcome : GWBReviewOutcome
  abstainOutcome : GWBReviewOutcome

record GWBReviewedHopBoundary : Set where
  constructor gwb-reviewed-hop-boundary
  field
    questionChosenFromCurrentFrontier : Bool
    questionChosenBeforeNetworkAcquisition : Bool
    exactSourceManifestationBoundToReview : Bool
    exactEvidenceDigestBoundToReview : Bool
    selectedMoveBoundToReview : Bool
    frontierDigestBoundToReview : Bool
    pendingBundleIsPersistenceAuthority : Bool
    reviewedNegativeMaySuppressExactMove : Bool
    negativeOutcomeAutomaticallyClosesResidual : Bool
    reviewedPositiveMayOpenNewResiduals : Bool
    priorReviewedMoveMayReplayWithoutNewEvidence : Bool
    reviewedStateAndTrajectoryCommitAtomically : Bool
    hopReceiptCreatesSemanticAuthority : Bool
    hopReceiptPromotesApplicability : Bool
    hopReceiptPromotesClaimTruth : Bool

open GWBReviewedHopBoundary public

canonicalReviewedHopBoundary : GWBReviewedHopBoundary
canonicalReviewedHopBoundary =
  gwb-reviewed-hop-boundary
    true true true true true true
    false
    true false true false true
    false false false

------------------------------------------------------------------------
-- Full campaign.
------------------------------------------------------------------------

record GWB100HopCampaignBoundary : Set where
  constructor gwb-100-hop-campaign-boundary
  field
    reviewedHopTarget : Nat
    existingGwbWorldReadyCarrierReused : Bool
    oneCommittedHopMeansOneReviewedInformationMove : Bool
    hopCountEqualsNovelQidCount : Bool
    hopCountEqualsTraversalDepth : Bool
    questionSelectedBeforeAcquisition : Bool
    acquisitionOccursBeforeParetoSelection : Bool
    reviewAvailabilityIsSchedulerPrior : Bool
    freshDiagnosisAfterEveryCommittedHop : Bool
    p31MayActAsTypeDiscriminator : Bool
    p279MayActAsSuperclassDiscriminator : Bool
    p31IsMandatoryTraversalStep : Bool
    p279IsMandatoryTraversalStep : Bool
    inverseSubclassRequiresGovernedProvider : Bool
    p279AdjacencyAutomaticallyCreatesSubclassObligation : Bool
    multilingualWikipediaSurfacesArePeers : Bool
    sameQidCreatesSemanticEquivalence : Bool
    paretoDimensionsScalarized : Bool
    frontierRankCreatesTruthRank : Bool
    reviewedNegativeMaySuppressExactMove : Bool
    negativeOutcomeAutomaticallyClosesResidual : Bool
    reviewedPositiveMayOpenNewResiduals : Bool
    externalOntologyOnlyAfterNarrowResidual : Bool
    broadSnowballOnlyAfterNarrowerResidual : Bool
    hundredHopCompletionPaysConsumerClosure : Bool
    campaignCandidateOnly : Bool
    campaignCreatesSemanticAuthority : Bool
    campaignPromotesApplicability : Bool
    campaignPromotesClaimTruth : Bool

open GWB100HopCampaignBoundary public

canonicalGWB100HopCampaign : GWB100HopCampaignBoundary
canonicalGWB100HopCampaign =
  gwb-100-hop-campaign-boundary
    100
    true
    true
    false
    false
    true
    false
    false
    true
    true
    true
    false
    false
    true
    false
    true
    false
    false
    false
    true
    false
    true
    true
    true
    false
    true
    false
    false
    false

------------------------------------------------------------------------
-- Existing owners are literal anchors, not inspiration-only references.
------------------------------------------------------------------------

gwbRoadmapAnchor : Roadmap.GWBExecutionBoundary
gwbRoadmapAnchor = Roadmap.canonicalGWBExecutionBoundary

gwbCarrierAnchor : Carrier.GWBCandidateWorldBoundary
gwbCarrierAnchor = Carrier.canonicalGWBCandidateWorldBoundary

worldResearchBudgetAnchor : Budget.WorldResearchIterationBudget
worldResearchBudgetAnchor = Budget.canonicalWorldResearchIterationBudget

wikimediaFirstAnchor : Wikimedia.WikimediaFirstAcquisitionPolicy
wikimediaFirstAnchor = Wikimedia.canonicalWikimediaFirstAcquisitionPolicy

externalOntologyAnchor : External.ExternalOntologyPolicy
externalOntologyAnchor = External.canonicalExternalOntologyPolicy

nDimParetoAnchor : NDim.NDimParetoHyperfabricBoundary
nDimParetoAnchor = NDim.canonicalNDimParetoHyperfabricBoundary

experimentalCoordinateAnchor : Experiment.ExperimentalCoordinateBoundary
experimentalCoordinateAnchor = Experiment.canonicalExperimentalCoordinateBoundary

snowballDiscoveryAnchor : Snowball.SnowballDiscoveryBoundary
snowballDiscoveryAnchor = Snowball.canonicalSnowballDiscoveryBoundary

leastPrivilegeAnchor : LeastPrivilege.ProofSearchLeastPrivilegeBoundary
leastPrivilegeAnchor = LeastPrivilege.canonicalProofSearchLeastPrivilegeBoundary

highestAlphaAnchor : HighestAlpha.HighestAlphaObservationBoundary
highestAlphaAnchor = HighestAlpha.canonicalHighestAlphaObservationBoundary

returnLoopAnchor : ReturnLoop.ExecutableWorldResearchLoopBoundary
returnLoopAnchor = ReturnLoop.canonicalExecutableWorldResearchLoopBoundary

assessmentAnchor : Assessment.AcquisitionResultAssessmentBoundary
assessmentAnchor = Assessment.canonicalAcquisitionResultAssessmentBoundary

frontierActionAnchor : FrontierAction.LegalFeedbackCompatibilityBoundary
frontierActionAnchor = FrontierAction.canonicalLegalFeedbackCompatibilityBoundary

------------------------------------------------------------------------
-- Fail-closed non-collapse laws.
------------------------------------------------------------------------

data HopEqualsQid : Set where
data HopEqualsGraphDepth : Set where
data ParetoRankEqualsTruthRank : Set where
data P31ObservationEqualsTypeTruth : Set where
data P279ObservationCreatesInverseSubclassDebt : Set where
data SharedQidEqualsSemanticEquivalence : Set where
data PendingReviewBundleEqualsAuthority : Set where
data NegativeResultEqualsResidualPayment : Set where
data HundredHopsEqualConsumerClosure : Set where
data AcquisitionEqualsEvidencePayment : Set where

hopDoesNotEqualQid : HopEqualsQid → ⊥
hopDoesNotEqualQid ()

hopDoesNotEqualGraphDepth : HopEqualsGraphDepth → ⊥
hopDoesNotEqualGraphDepth ()

paretoRankDoesNotEqualTruth : ParetoRankEqualsTruthRank → ⊥
paretoRankDoesNotEqualTruth ()

p31ObservationDoesNotCreateTypeTruth : P31ObservationEqualsTypeTruth → ⊥
p31ObservationDoesNotCreateTypeTruth ()

p279ObservationDoesNotCreateInverseDebt :
  P279ObservationCreatesInverseSubclassDebt → ⊥
p279ObservationDoesNotCreateInverseDebt ()

sharedQidDoesNotCreateSemanticEquivalence :
  SharedQidEqualsSemanticEquivalence → ⊥
sharedQidDoesNotCreateSemanticEquivalence ()

pendingBundleDoesNotCreateAuthority :
  PendingReviewBundleEqualsAuthority → ⊥
pendingBundleDoesNotCreateAuthority ()

negativeResultDoesNotPayResidual :
  NegativeResultEqualsResidualPayment → ⊥
negativeResultDoesNotPayResidual ()

hundredHopsDoNotPayConsumerClosure :
  HundredHopsEqualConsumerClosure → ⊥
hundredHopsDoNotPayConsumerClosure ()

acquisitionDoesNotEqualPayment :
  AcquisitionEqualsEvidencePayment → ⊥
acquisitionDoesNotEqualPayment ()
