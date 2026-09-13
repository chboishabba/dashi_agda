module DASHI.Reasoning.FibreRoutingMaleCNSCompressionEmpiricalSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DrosophilaJoinedObserverSourceSnowballExact as Source
import DASHI.Reasoning.FibreRoutingJoinedObserverEmpiricalFrontierExact as Joined
import DASHI.Reasoning.FibreRoutingCompressionLadderExact as Ladder
import DASHI.Reasoning.FibreRoutingCompressionIbrahimSnowballExact as Ibrahim
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal

------------------------------------------------------------------------
-- REAL MALECNS NESTED COMPRESSION RECEIPT
--
-- Numerical authority remains the dashiBRAIN JSON artefact.  This owner stores
-- exact string-valued observations and promotion gates only.  The one-fibre
-- result is a held-out compression observation, not a receptor-resolved or
-- causal mechanism proof.
------------------------------------------------------------------------

record MaleCNSCompressionReceipt : Set where
  constructor malecns-compression-receipt
  field
    repository : String
    branch : String
    runtimeCommit : String
    artifactPath : String
    trialIdentity : String
    testReceipt : String
    sourceFibreCount : Nat
    selectedFibreCountMean : String
    fullJoinedResidual : String
    compressedOuterResidual : String
    residualDelta : String
    tolerance : String
    outerFoldCount : Nat
    signedReverseSelections : Nat
    signedForwardSelections : Nat
    dominantFibreReading : String
    scientificBoundary : String

open MaleCNSCompressionReceipt public

currentMaleCNSCompression : MaleCNSCompressionReceipt
currentMaleCNSCompression =
  malecns-compression-receipt
    "github.com/chboishabba/dashiBRAIN"
    "agent/malecns-real-benchmark-tranche"
    "a35607970756483fd35f81f5c5fa9832c3fceffc"
    "data/gauthey_lbm/jrc2018_regions_a2_r5/malecns_fibre_compression_ladder.json"
    "04032024_6f_a2_r5"
    "170/170 full pytest suite; 24/24 targeted compression/survival tests"
    8
    "1.0"
    "0.1364"
    "0.1318"
    "-0.0046"
    "0.01"
    26
    25
    1
    "Nested inner-LORO selected signed_reverse in 25/26 outer folds and signed_forward in AOTU; every outer fold selected exactly one fibre."
    "The result establishes a compact held-out predictive carrier for this session and consumer only. It does not establish neurotransmitter-sign causality, receptor-resolved physiology, pair-specific wiring, population generalization, or uniqueness outside the declared candidate family."

------------------------------------------------------------------------
-- Promotion gates.
------------------------------------------------------------------------

data CompressionPromotionGate : Set where
  nestedSelectionExecutedGate : CompressionPromotionGate
  oneFibreCompressionObservedGate : CompressionPromotionGate
  heldOutImprovementObservedGate : CompressionPromotionGate
  selectedFibreStableGate : CompressionPromotionGate
  transmitterSignSpecificityGate : CompressionPromotionGate
  senderAssignmentSpecificityGate : CompressionPromotionGate
  pairSpecificWiringGate : CompressionPromotionGate
  independentReplicationGate : CompressionPromotionGate
  populationGeneralizationGate : CompressionPromotionGate

record CompressionGateState : Set where
  constructor compression-gate-state
  field
    gate : CompressionPromotionGate
    paid : Bool
    evidenceReference : String

open CompressionGateState public

nestedSelectionExecuted : CompressionGateState
nestedSelectionExecuted =
  compression-gate-state nestedSelectionExecutedGate true
    "nested inner-LORO subset selection executed on each of 26 untouched outer region folds"

oneFibreCompressionObserved : CompressionGateState
oneFibreCompressionObserved =
  compression-gate-state oneFibreCompressionObservedGate true
    "mean selected fibre count 1.0; no outer fold selected two or more fibres"

heldOutImprovementObserved : CompressionGateState
heldOutImprovementObserved =
  compression-gate-state heldOutImprovementObservedGate true
    "weighted mean outer residual 0.1318 versus joined 8-fibre residual 0.1364"

selectedFibreStable : CompressionGateState
selectedFibreStable =
  compression-gate-state selectedFibreStableGate true
    "signed_reverse selected in 25/26 outer folds; signed_forward selected once"

transmitterSignSpecificity : CompressionGateState
transmitterSignSpecificity =
  compression-gate-state transmitterSignSpecificityGate false
    "not paid by subset selection alone; compare signed_reverse against unsigned and magnitude-only controls"

senderAssignmentSpecificity : CompressionGateState
senderAssignmentSpecificity =
  compression-gate-state senderAssignmentSpecificityGate false
    "not paid by subset selection alone; preserve unsigned connectivity while perturbing sender-specific sign assignment"

pairSpecificWiring : CompressionGateState
pairSpecificWiring =
  compression-gate-state pairSpecificWiringGate false
    "joined decision-target strength and label nulls remain non-rejected"

independentReplication : CompressionGateState
independentReplication =
  compression-gate-state independentReplicationGate false
    "single Gauthey recording 04032024_6f_a2_r5"

populationGeneralization : CompressionGateState
populationGeneralization =
  compression-gate-state populationGeneralizationGate false
    "requires additional trials/animals and same-object source/registration receipts"

------------------------------------------------------------------------
-- Current dashiBRAIN discriminator frontier.
--
-- The runtime branch has already advanced past the compression receipt to a
-- narrower signed-fibre discriminator.  This is acquisition progress, not a
-- result claim: no output from that discriminator is promoted here.
------------------------------------------------------------------------

record DiscriminatorFrontier : Set where
  constructor discriminator-frontier
  field
    repositoryHead : String
    producerPath : String
    question : String
    preservesUnsignedPairwiseConnectivity : Bool
    comparesMagnitudeOnly : Bool
    comparesSenderPatternPermutation : Bool
    executionReceiptPaid : Bool
    interpretation : String

open DiscriminatorFrontier public

currentSignedFibreDiscriminatorFrontier : DiscriminatorFrontier
currentSignedFibreDiscriminatorFrontier =
  discriminator-frontier
    "3c02daf6033c1244d8aa8e59fe9f478f19985259"
    "dashi/analysis/signed_fibre_discriminator.py"
    "Does the compressed signed_reverse carrier use transmitter polarity/sender assignment beyond unsigned magnitude-direction geometry?"
    true
    true
    true
    false
    "Producer exists at current branch head, but this formal owner has no same-object execution output yet; polarity/sender-specific mechanism remains unpaid."

------------------------------------------------------------------------
-- Ibrahim-style DASHI knowledge coordinates.
--
-- These edges describe typed navigation/provenance in the repository.  They do
-- not turn citation, QID or Dewey adjacency into theorem implication.
------------------------------------------------------------------------

flySourceCoordinate : Traversal.DashiKnowledgeCoordinate
flySourceCoordinate =
  Traversal.dashi-knowledge-coordinate
    "DASHI/Biology/DrosophilaJoinedObserverSourceSnowballExact.agda"
    "Drosophila joined-observer primary-source chain"
    "570.000 / 612.8 candidate"
    "publication QIDs unresolved; DOI identities primary"
    "Gauthey 10.1038/s41467-026-72437-1; BIFROST 10.1073/pnas.2322687121; JRC2018 10.1371/journal.pone.0236495; VFB 10.3389/fphys.2023.1076533; MaleCNS 10.1016/j.cell.2026.08.015"

joinedEmpiricalCoordinate : Traversal.DashiKnowledgeCoordinate
joinedEmpiricalCoordinate =
  Traversal.dashi-knowledge-coordinate
    "DASHI/Reasoning/FibreRoutingJoinedObserverEmpiricalFrontierExact.agda"
    "joined overlap+stimulus empirical decision frontier"
    "570.000 / 612.8 candidate"
    "not-applicable: local empirical receipt"
    "dashiBRAIN:malecns_joined_observer_ndim.json"

compressionCoordinate : Traversal.DashiKnowledgeCoordinate
compressionCoordinate =
  Traversal.dashi-knowledge-coordinate
    "DASHI/Reasoning/FibreRoutingMaleCNSCompressionEmpiricalSnowballExact.agda"
    "MaleCNS nested one-fibre compression frontier"
    "570.000 / 612.8 candidate"
    "not-applicable: local empirical receipt"
    "dashiBRAIN:malecns_fibre_compression_ladder.json@a35607970756483fd35f81f5c5fa9832c3fceffc"

compressionTheoryCoordinate : Traversal.DashiKnowledgeCoordinate
compressionTheoryCoordinate =
  Traversal.dashi-knowledge-coordinate
    "DASHI/Reasoning/FibreRoutingCompressionIbrahimSnowballExact.agda"
    "consumer-relative compression / distillation / MoE / grokking source atlas"
    "006.31 machine learning; 005.746 data compression; unresolved narrower techniques"
    "Q2539; Q2493; Q1417790; Q30688561; Q126362531; unresolved technique QIDs retained"
    "Rissanen 10.1016/0005-1098(78)90005-5; Jacobs 10.1162/neco.1991.3.1.79; arXiv source identities retained for distillation/pruning/sparse-MoE/grokking/LoRA"

sourceSupportsJoinedEmpirical : Traversal.DashiFirstLinkEdge
sourceSupportsJoinedEmpirical =
  Traversal.dashi-first-link-edge
    joinedEmpiricalCoordinate
    flySourceCoordinate
    Traversal.supportedBy
    Traversal.canonicalDashiFirstLinkPolicy
    "functional, registration, atlas and connectome claims must trace to their typed primary-source roles"
    true

compressionDependsOnJoinedEmpirical : Traversal.DashiFirstLinkEdge
compressionDependsOnJoinedEmpirical =
  Traversal.dashi-first-link-edge
    compressionCoordinate
    joinedEmpiricalCoordinate
    Traversal.dependsOn
    Traversal.canonicalDashiFirstLinkPolicy
    "nested compression uses the joined stimulus+overlap decision target as the held-out consumer"
    true

compressionCrossPollinatesWithTheory : Traversal.DashiFirstLinkEdge
compressionCrossPollinatesWithTheory =
  Traversal.dashi-first-link-edge
    compressionCoordinate
    compressionTheoryCoordinate
    Traversal.crossPollinatesWith
    Traversal.canonicalDashiFirstLinkPolicy
    "the real Fly experiment instantiates consumer-relative compression but does not inherit ML mechanism claims from adjacency"
    true

------------------------------------------------------------------------
-- Cross-pollination anchors and firewalls.
------------------------------------------------------------------------

sourceBoundary : Source.SourceSnowballBoundary
sourceBoundary = Source.canonicalSourceSnowballBoundary

joinedBoundary : Joined.EmpiricalFrontierBoundary
joinedBoundary = Joined.canonicalEmpiricalFrontierBoundary

compressionBoundary : Ladder.FibreCompressionLadderBoundary
compressionBoundary = Ladder.canonicalFibreCompressionLadderBoundary

ibrahimBoundary : Ibrahim.FibreCompressionIbrahimSnowballBoundary
ibrahimBoundary = Ibrahim.canonicalFibreCompressionIbrahimSnowballBoundary

record MaleCNSCompressionSnowballBoundary : Set where
  constructor malecns-compression-snowball-boundary
  field
    oneFibreResultIsHeldOutObservation : Bool
    oneFibreResultImpliesUniqueBiologicalMechanism : Bool
    signedReverseSelectionImpliesTransmitterSignCausality : Bool
    signedReverseSelectionImpliesPairSpecificWiring : Bool
    lowerOuterResidualAutomaticallyRejectsEarlierNulls : Bool
    compressionMayBeRankedBeforeConsumerAdequacy : Bool
    qidDeweyCitationCreateEmpiricalPayment : Bool
    acquisitionMaySnowballToDiscriminatorsBeforeReplication : Bool
    promotionMaySkipDiscriminatorOrReplicationReceipts : Bool
    negativeEarlierNullsRemainAppendOnly : Bool

canonicalMaleCNSCompressionSnowballBoundary : MaleCNSCompressionSnowballBoundary
canonicalMaleCNSCompressionSnowballBoundary =
  malecns-compression-snowball-boundary
    true false false false false false false true false true
