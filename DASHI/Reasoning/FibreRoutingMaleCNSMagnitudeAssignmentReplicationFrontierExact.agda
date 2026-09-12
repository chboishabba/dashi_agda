module DASHI.Reasoning.FibreRoutingMaleCNSMagnitudeAssignmentReplicationFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.FibreRoutingMaleCNSPolarityAndJointQuotientSnowballExact as Polarity
import DASHI.Reasoning.FibreRoutingMaleCNSScaleShapeEmpiricalSnowballExact as ScaleShape
import DASHI.Reasoning.FibreRoutingCompressionIbrahimSnowballExact as Ibrahim
import DASHI.Reasoning.FibreRoutingSufficiencyCausalInterventionSnowballExact as Causal
import DASHI.Biology.DrosophilaSignedFibreAnatomySourceSnowballExact as Anatomy
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal

------------------------------------------------------------------------
-- SCALE-FREE SENDER-MAGNITUDE ASSIGNMENT NULL / REPLICATION FRONTIER
--
-- Current candidate carrier:
--   G_ij = m_i P_ij
-- where P is row-relative unsigned wiring shape and m is a sender-magnitude
-- field.  This owner keeps two different magnitude definitions distinct:
--
--   mNet_i = | sum_j S_ij | / sum_j |D_ij| = |a_i|
--   mAbs_i =   sum_j |S_ij| / sum_j |D_ij|
--
-- They coincide only when mixed-sign cancellation is absent/negligible.
-- The null keeps P and the full multiset of mNet values fixed and permutes only
-- the anatomical assignment i -> m_i.
--
-- IMPORTANT: failure to reject this null does NOT prove exchangeability or
-- certify the unordered multiset as a sufficient statistic.  It means only
-- that anatomical indexing was not distinguished by this declared test.
------------------------------------------------------------------------

record MagnitudeAssignmentReceipt : Set where
  constructor magnitude-assignment-receipt
  field
    repository : String
    branch : String
    runtimeCommit : String
    artifactPath : String
    trialIdentity : String
    testReceipt : String
    regionCount : Nat
    nullCount : Nat
    netMagnitudeDefinition : String
    absoluteRatioMagnitudeDefinition : String
    carrierDefinition : String
    netMagnitudeResidual : String
    absoluteRatioMagnitudeResidual : String
    empiricalP : String
    nullMean : String
    nullMedian : String
    nullMinimum : String
    nullMaximum : String
    nullQ05 : String
    nullQ95 : String
    interpretation : String

open MagnitudeAssignmentReceipt public

currentMagnitudeAssignmentReceipt : MagnitudeAssignmentReceipt
currentMagnitudeAssignmentReceipt = magnitude-assignment-receipt
  "github.com/chboishabba/dashiBRAIN"
  "agent/malecns-real-benchmark-tranche"
  "60ce5efe85e4e01f0167369025fe8331373c7b81"
  "data/gauthey_lbm/jrc2018_regions_a2_r5/malecns_sender_magnitude_assignment_null.json"
  "04032024_6f_a2_r5"
  "189/189 full pytest suite; sender-magnitude definition and scale-free assignment tests included"
  26
  999
  "mNet_i = abs(sum_j S_ij) / sum_j abs(D_ij) = |a_i|"
  "mAbs_i = sum_j abs(S_ij) / sum_j abs(D_ij)"
  "G_ij = m_i * P_ij with P fixed and sender magnitude assignment permuted"
  "0.13189851095808636"
  "0.13190334413965168"
  "0.092"
  "0.1323707028509359"
  "0.13241684698041084"
  "0.13024176826166425"
  "0.13379754822015028"
  "0.13171611405101633"
  "0.13288240332155468"
  "For this single session and joined-controlled LORO consumer, anatomical assignment of the net sender-magnitude field is not distinguished by the 999-draw permutation test (p=0.092). The result does not prove exchangeability, multiset sufficiency, or population invariance."

------------------------------------------------------------------------
-- APPEND-ONLY REPLICATION ACQUISITION FRONTIER
--
-- Exact source-row identity recovery is a prerequisite for independent-trial
-- materialization, not itself a replication result.  The empirical receipt is
-- pinned to the commit that produced the currently paid 559/1620 artifact.
-- A distinct implementation-lineage coordinate may advance as recovery becomes
-- safer/resumable; code advancement does not retroactively alter the artifact.
------------------------------------------------------------------------

record ReplicationIdentityRecoveryReceipt : Set where
  constructor replication-identity-recovery-receipt
  field
    repository : String
    branch : String
    recoveryRuntimeCommit : String
    currentRecoveryImplementationCommit : String
    recoveryImplementationState : String
    accumulationArtifactPath : String
    accumulatedIdentityCsv : String
    depositedSelectedCount : Nat
    resolvedSelectedCount : Nat
    unresolvedSelectedCount : Nat
    searchedTrialCount : Nat
    a2r5ResolvedCount : Nat
    a1r9ResolvedCount : Nat
    a2r5TrialIdentity : String
    a1r9TrialIdentity : String
    a1r9RemoteArchiveAccessed : Bool
    exactTraceIdentitySemantics : String
    interpretation : String

open ReplicationIdentityRecoveryReceipt public

currentReplicationIdentityRecoveryReceipt : ReplicationIdentityRecoveryReceipt
currentReplicationIdentityRecoveryReceipt = replication-identity-recovery-receipt
  "github.com/chboishabba/dashiBRAIN"
  "agent/malecns-real-benchmark-tranche"
  "a9504ea00a30960a6728f90a5ff31b4d1f97ced6"
  "9d15d4acc622a87cdd0ebc5d2f22f8531b277ce7"
  "out-of-core pickle ingestion; blockwise scoring; standalone per-trial checkpoints; one-trial-at-a-time incremental merge; optional post-checkpoint source-ZIP release"
  "data/gauthey_lbm/reconstruction_all_available/gauthey_lbm_identity_accumulation.json"
  "data/gauthey_lbm/reconstruction_all_available/gauthey_lbm_selected_identities_accumulated.csv"
  1620
  559
  1061
  2
  374
  185
  "04032024_6f_a2_r5"
  "04192024_6f_a1_r9"
  false
  "exact trace equality to deposited selected row; not neuron identity and not atlas identity"
  "Two searched Gauthey LBM trials currently pay 559 of 1620 exact selected-row source identities. The remaining 1061 rows stay unresolved. The recovery implementation has since advanced to durable one-trial-at-a-time checkpointing, but those code changes do not themselves add empirical identities or pay independent-trial replication."

record ReplicationAcquisitionBoundary : Set where
  constructor replication-acquisition-boundary
  field
    exactSourceIdentityRecoveryStarted : Bool
    exactSourceIdentityRecoveryComplete : Bool
    searchedTrialReceiptsAppendOnly : Bool
    unresolvedRowsRemainExplicit : Bool
    perTrialCheckpointingImplemented : Bool
    accumulatedReceiptAdvancesAfterEachTrial : Bool
    sourceZipMayBeReleasedOnlyAfterDurableCheckpoint : Bool
    a1r9RecoveryRequiredRemoteArchiveAccess : Bool
    implementationAdvanceCreatesEmpiricalPayment : Bool
    sourceIdentityRecoveryImpliesIndependentTrialReplication : Bool
    sourceIdentityRecoveryImpliesJRC2018Ready : Bool
    sourceIdentityRecoveryImpliesCrossAnimalReplication : Bool

open ReplicationAcquisitionBoundary public

canonicalReplicationAcquisitionBoundary : ReplicationAcquisitionBoundary
canonicalReplicationAcquisitionBoundary = replication-acquisition-boundary
  true false true true true true true false false false false false

------------------------------------------------------------------------
-- Algebraic boundary: |sum S| and sum |S| are different operations.
------------------------------------------------------------------------

data MagnitudeDefinition : Set where
  netAfterCancellation : MagnitudeDefinition
  absoluteBeforeCancellation : MagnitudeDefinition

record MagnitudeDefinitionBoundary : Set where
  constructor magnitude-definition-boundary
  field
    netAndAbsoluteDefinitionsRetainedSeparately : Bool
    equalByDefinition : Bool
    nearEqualResidualsInThisSession : Bool
    nearEqualResidualsImplySameBiologicalQuantity : Bool

open MagnitudeDefinitionBoundary public

canonicalMagnitudeDefinitionBoundary : MagnitudeDefinitionBoundary
canonicalMagnitudeDefinitionBoundary = magnitude-definition-boundary
  true false true false

------------------------------------------------------------------------
-- Promotion gates.
------------------------------------------------------------------------

data MagnitudeAssignmentGate : Set where
  scaleFreeMagnitudeNullExecutedGate : MagnitudeAssignmentGate
  magnitudeMultisetPreservedGate : MagnitudeAssignmentGate
  relativeWiringShapePreservedGate : MagnitudeAssignmentGate
  anatomicalMagnitudeAssignmentDistinguishedGate : MagnitudeAssignmentGate
  unorderedMagnitudeMultisetSufficientGate : MagnitudeAssignmentGate
  anatomicalIndexingProvablyUnnecessaryGate : MagnitudeAssignmentGate
  netVsAbsoluteMagnitudeMechanismGate : MagnitudeAssignmentGate
  sameSessionCompressionLadderClosedGate : MagnitudeAssignmentGate
  independentTrialReplicationGate : MagnitudeAssignmentGate
  crossAnimalReplicationGate : MagnitudeAssignmentGate
  populationGeneralizationGate : MagnitudeAssignmentGate

record MagnitudeAssignmentGateState : Set where
  constructor magnitude-assignment-gate-state
  field
    gate : MagnitudeAssignmentGate
    paid : Bool
    evidenceReference : String

open MagnitudeAssignmentGateState public

scaleFreeMagnitudeNullExecuted : MagnitudeAssignmentGateState
scaleFreeMagnitudeNullExecuted = magnitude-assignment-gate-state scaleFreeMagnitudeNullExecutedGate true
  "999-draw scale-free sender-magnitude assignment null executed on mNet_i * P_ij"

magnitudeMultisetPreserved : MagnitudeAssignmentGateState
magnitudeMultisetPreserved = magnitude-assignment-gate-state magnitudeMultisetPreservedGate true
  "null permutes anatomical assignment while preserving the observed magnitude multiset"

relativeWiringShapePreserved : MagnitudeAssignmentGateState
relativeWiringShapePreserved = magnitude-assignment-gate-state relativeWiringShapePreservedGate true
  "row-relative wiring shape P remains fixed in every null draw"

anatomicalMagnitudeAssignmentDistinguished : MagnitudeAssignmentGateState
anatomicalMagnitudeAssignmentDistinguished = magnitude-assignment-gate-state anatomicalMagnitudeAssignmentDistinguishedGate false
  "empirical p=0.092; declared test does not reject anatomical reassignment"

unorderedMagnitudeMultisetSufficient : MagnitudeAssignmentGateState
unorderedMagnitudeMultisetSufficient = magnitude-assignment-gate-state unorderedMagnitudeMultisetSufficientGate false
  "non-rejection of assignment null does not certify an unordered multiset as sufficient for this or future consumers"

anatomicalIndexingProvablyUnnecessary : MagnitudeAssignmentGateState
anatomicalIndexingProvablyUnnecessary = magnitude-assignment-gate-state anatomicalIndexingProvablyUnnecessaryGate false
  "absence of significance is not a proof of equivalence or dispensability"

netVsAbsoluteMagnitudeMechanism : MagnitudeAssignmentGateState
netVsAbsoluteMagnitudeMechanism = magnitude-assignment-gate-state netVsAbsoluteMagnitudeMechanismGate false
  "mNetP and mAbsP residuals are nearly identical in this session, but the algebraic quantities are distinct and no causal interpretation is paid"

sameSessionCompressionLadderClosed : MagnitudeAssignmentGateState
sameSessionCompressionLadderClosed = magnitude-assignment-gate-state sameSessionCompressionLadderClosedGate true
  "after direct scale, polarity, sender-scalar, low-rank, and sender-magnitude assignment discriminators, replication has higher information value than another same-session quotient search"

independentTrialReplication : MagnitudeAssignmentGateState
independentTrialReplication = magnitude-assignment-gate-state independentTrialReplicationGate false
  "replication acquisition has recovered 559/1620 exact selected-row source identities across a2_r5 and a1_r9, but no independent recording has yet been materialized on the frozen 26-region JRC2018 carrier and scored under the same factorized protocol"

crossAnimalReplication : MagnitudeAssignmentGateState
crossAnimalReplication = magnitude-assignment-gate-state crossAnimalReplicationGate false
  "same carrier not yet shown on an independent animal with same-object source/registration receipts"

populationGeneralization : MagnitudeAssignmentGateState
populationGeneralization = magnitude-assignment-gate-state populationGeneralizationGate false
  "requires trial/animal replication and explicit pooling/generalization contract"

------------------------------------------------------------------------
-- Current best bounded reading.
------------------------------------------------------------------------

record CurrentCarrierReading : Set where
  constructor current-carrier-reading
  field
    retainedRelativeShape : Bool
    retainedSenderMagnitudeDistribution : Bool
    anatomicalMagnitudeIndexingRequiredByCurrentTest : Bool
    anatomicalMagnitudeIndexingProvedIrrelevant : Bool
    binaryPolarityRequiredByCurrentTest : Bool
    absoluteSenderScaleRequiredByCurrentTest : Bool
    pairSpecificSignedRatioRequiredByCurrentTest : Bool
    reading : String

open CurrentCarrierReading public

currentCarrierReading : CurrentCarrierReading
currentCarrierReading = current-carrier-reading
  true true false false false false false
  "Best same-session compression reading: relative wiring shape P plus the observed sender-gain magnitude distribution is enough to define the tested candidate family, while anatomical indexing is not distinguished by the current permutation test. This is not yet a certified quotient or a population-level minimal carrier."

------------------------------------------------------------------------
-- Ibrahim traversal / source coordinates.
------------------------------------------------------------------------

magnitudeAssignmentCoordinate : Traversal.DashiKnowledgeCoordinate
magnitudeAssignmentCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Reasoning/FibreRoutingMaleCNSMagnitudeAssignmentReplicationFrontierExact.agda"
  "scale-free sender-magnitude assignment null and replication frontier"
  "570.000 / 612.8 neuroscience candidate"
  "Q130888 Drosophila; Q162657 neurotransmitter; local empirical object has no external QID"
  "dashiBRAIN:malecns_sender_magnitude_assignment_null.json@60ce5efe85e4e01f0167369025fe8331373c7b81"

replicationIdentityRecoveryCoordinate : Traversal.DashiKnowledgeCoordinate
replicationIdentityRecoveryCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Reasoning/FibreRoutingMaleCNSMagnitudeAssignmentReplicationFrontierExact.agda"
  "Gauthey exact selected-row identity recovery frontier"
  "570.000 / 612.8 neuroscience candidate"
  "same Gauthey source family; local acquisition receipt has no external QID"
  "dashiBRAIN:gauthey_lbm_identity_accumulation.json@a9504ea00a30960a6728f90a5ff31b4d1f97ced6; recovery implementation head 9d15d4acc622a87cdd0ebc5d2f22f8531b277ce7"

polarityCoordinate : Traversal.DashiKnowledgeCoordinate
polarityCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Reasoning/FibreRoutingMaleCNSPolarityAndJointQuotientSnowballExact.agda"
  "exact polarity null / joint quotient frontier"
  "570.000 / 612.8 neuroscience candidate"
  "Q130888; Q162657; source identity is coordinate only"
  "dashiBRAIN:malecns_sender_scalar_polarity_null.json"

magnitudeDependsOnPolarityFrontier : Traversal.DashiFirstLinkEdge
magnitudeDependsOnPolarityFrontier = Traversal.dashi-first-link-edge
  magnitudeAssignmentCoordinate polarityCoordinate Traversal.dependsOn
  Traversal.canonicalDashiFirstLinkPolicy
  "sender-magnitude assignment is the remaining same-session discriminator after polarity fails and scale-free relative shape remains competitive"
  true

------------------------------------------------------------------------
-- Existing boundaries reused.
------------------------------------------------------------------------

polarityBoundary : Polarity.PolarityJointQuotientBoundary
polarityBoundary = Polarity.canonicalPolarityJointQuotientBoundary

scaleShapeBoundary : ScaleShape.MaleCNSScaleShapeBoundary
scaleShapeBoundary = ScaleShape.canonicalMaleCNSScaleShapeBoundary

ibrahimBoundary : Ibrahim.FibreCompressionIbrahimSnowballBoundary
ibrahimBoundary = Ibrahim.canonicalFibreCompressionIbrahimSnowballBoundary

causalBoundary : Causal.FibreSufficiencyCausalInterventionBoundary
causalBoundary = Causal.canonicalFibreSufficiencyCausalInterventionBoundary

anatomyBoundary : Anatomy.SignedFibreAnatomySourceBoundary
anatomyBoundary = Anatomy.canonicalSignedFibreAnatomySourceBoundary

record MagnitudeReplicationBoundary : Set where
  constructor magnitude-replication-boundary
  field
    magnitudeAssignmentNullExecuted : Bool
    anatomyIndexedGainDistinguished : Bool
    nonSignificancePromotesExchangeability : Bool
    nonSignificancePromotesSufficiency : Bool
    netMagnitudeEqualsAbsoluteMagnitudeByDefinition : Bool
    sameSessionQuotientSearchShouldContinueIndefinitely : Bool
    replicationIsNextHighAlphaStep : Bool
    partialExactReplicationSourceIdentityRecoveryPaid : Bool
    partialIdentityRecoveryPromotesReplication : Bool
    qidDeweyDoiLinkCreateEmpiricalPayment : Bool
    negativeResultsRemainAppendOnly : Bool

open MagnitudeReplicationBoundary public

canonicalMagnitudeReplicationBoundary : MagnitudeReplicationBoundary
canonicalMagnitudeReplicationBoundary = magnitude-replication-boundary
  true false false false false false true true false false true
