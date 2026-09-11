module DASHI.Reasoning.FibreRoutingMaleCNSSenderScalarCompressionSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DrosophilaSignedFibreAnatomySourceSnowballExact as Anatomy
import DASHI.Reasoning.FibreRoutingMaleCNSCompressionEmpiricalSnowballExact as Previous
import DASHI.Reasoning.FibreRoutingCompressionLadderExact as Ladder
import DASHI.Reasoning.FibreRoutingCompressionIbrahimSnowballExact as Ibrahim
import DASHI.Reasoning.FibreRoutingSufficiencyCausalInterventionSnowballExact as Causal
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal

------------------------------------------------------------------------
-- REAL MALECNS SIGNED-FIBRE SECOND-STAGE COMPRESSION
--
-- Previous stage: 8 structural fibres -> one signed_reverse matrix fibre.
-- Current stage: signed matrix S -> unsigned D plus a sender tendency field a_i,
-- with a parallel low-rank ladder over R = S/D on non-zero D support.
--
-- Numerical authority remains the dashiBRAIN JSON artifact.  All numerical
-- observations are stored as strings; no p-value or residual becomes a proof.
------------------------------------------------------------------------

record SenderScalarCompressionReceipt : Set where
  constructor sender-scalar-compression-receipt
  field
    repository : String
    branch : String
    runtimeCommit : String
    artifactPath : String
    trialIdentity : String
    testReceipt : String
    regionCount : Nat
    sourceMatrixEntryCount : Nat
    senderScalarCount : Nat
    trueSignedReverseResidual : String
    senderScalarResidual : String
    unsignedReverseResidual : String
    senderPermutationNullMean : String
    senderPermutationP : String
    senderScalarGapToTrue : String
    recoveredSignedAdvantageReading : String
    bestTestedLowRank : Nat
    bestTestedLowRankResidual : String
    scientificBoundary : String

open SenderScalarCompressionReceipt public

currentSenderScalarCompression : SenderScalarCompressionReceipt
currentSenderScalarCompression = sender-scalar-compression-receipt
  "github.com/chboishabba/dashiBRAIN"
  "agent/malecns-real-benchmark-tranche"
  "817689a1b0b2403513fdcd329ba8f264551a091d"
  "data/gauthey_lbm/jrc2018_regions_a2_r5/malecns_signed_fibre_compression.json"
  "04032024_6f_a2_r5"
  "176/176 full pytest suite; 10/10 focused signed-fibre compression tests"
  26 676 26
  "0.13164"
  "0.13180"
  "0.13265"
  "0.13242"
  "0.0198 from preceding sender-pattern discriminator (2/101 empirical tail count)"
  "+0.00016"
  "Using displayed rounded residuals, the sender-scalar carrier recovers about 84.2% of the true signed layer's improvement over unsigned reverse; treat as approximate session-specific descriptive compression, not an exact invariant."
  8
  "0.13158"
  "For this single session and joined held-out consumer, most predictive advantage of the signed matrix is retained by unsigned D plus one scalar per sender neuropil. This does not establish receptor-resolved excitation/inhibition, causal transmitter mechanism, or population generalization."

record LowRankPoint : Set where
  constructor low-rank-point
  field rank : Nat
        residual : String
open LowRankPoint public

rank1 : LowRankPoint
rank1 = low-rank-point 1 "0.13197"
rank2 : LowRankPoint
rank2 = low-rank-point 2 "0.13199"
rank3 : LowRankPoint
rank3 = low-rank-point 3 "0.13193"
rank4 : LowRankPoint
rank4 = low-rank-point 4 "0.13188"
rank5 : LowRankPoint
rank5 = low-rank-point 5 "0.13178"
rank6 : LowRankPoint
rank6 = low-rank-point 6 "0.13171"
rank7 : LowRankPoint
rank7 = low-rank-point 7 "0.13165"
rank8 : LowRankPoint
rank8 = low-rank-point 8 "0.13158"

------------------------------------------------------------------------
-- Selected regional scalar observations.  These are local output coordinates,
-- not literature-derived constants.  External literature is only context.
------------------------------------------------------------------------

record RegionalScalarObservation : Set where
  constructor regional-scalar-observation
  field
    region : String
    value : String
    externalContext : String
    sameObjectLiteratureValidation : Bool
open RegionalScalarObservation public

alphaLobeScalar : RegionalScalarObservation
alphaLobeScalar = regional-scalar-observation
  "aL" "+0.891"
  "Kenyon-cell mushroom-body output is experimentally cholinergic; see Anatomy.barnstedtKenyonOutput"
  false

betaLobeScalar : RegionalScalarObservation
betaLobeScalar = regional-scalar-observation
  "bL" "+0.868"
  "Kenyon-cell mushroom-body output is experimentally cholinergic; see Anatomy.barnstedtKenyonOutput"
  false

gammaLobeScalar : RegionalScalarObservation
gammaLobeScalar = regional-scalar-observation
  "gL" "+0.779"
  "Kenyon-cell mushroom-body output is experimentally cholinergic; see Anatomy.barnstedtKenyonOutput"
  false

pedunculusScalar : RegionalScalarObservation
pedunculusScalar = regional-scalar-observation
  "PED" "+0.776"
  "mushroom-body/Kenyon-cell anatomy supplies contextual interpretation only"
  false

antennalLobeScalar : RegionalScalarObservation
antennalLobeScalar = regional-scalar-observation
  "AL" "+0.706"
  "cholinergic antennal-lobe relay neurons are supported by Anatomy.yasuyamaAntennalLobeRelay; AL also contains other transmitter classes"
  false

bulbScalar : RegionalScalarObservation
bulbScalar = regional-scalar-observation
  "BU" "-0.357"
  "GABAergic ring-neuron circuitry with dendrites in the bulb is supported by Anatomy.xieRingNeuronGaba; this does not support an 'entire bulb exclusively inhibitory' claim"
  false

------------------------------------------------------------------------
-- Promotion gates.
------------------------------------------------------------------------

data SenderCompressionGate : Set where
  senderScalarCompressionExecutedGate : SenderCompressionGate
  approximateSenderScalarRetentionGate : SenderCompressionGate
  lowRankCompressionExecutedGate : SenderCompressionGate
  senderAssignmentDiscriminatorGate : SenderCompressionGate
  polaritySpecificityGate : SenderCompressionGate
  targetSpecificRatioDispensabilityGate : SenderCompressionGate
  receptorResolvedMechanismGate : SenderCompressionGate
  independentReplicationGate : SenderCompressionGate
  populationGeneralizationGate : SenderCompressionGate

record SenderCompressionGateState : Set where
  constructor sender-compression-gate-state
  field gate : SenderCompressionGate
        paid : Bool
        evidenceReference : String
open SenderCompressionGateState public

senderScalarCompressionExecuted : SenderCompressionGateState
senderScalarCompressionExecuted = sender-compression-gate-state senderScalarCompressionExecutedGate true
  "malecns_signed_fibre_compression.json executed at dashiBRAIN 817689a1b0b2403513fdcd329ba8f264551a091d"

approximateSenderScalarRetention : SenderCompressionGateState
approximateSenderScalarRetention = sender-compression-gate-state approximateSenderScalarRetentionGate true
  "sender scalar residual 0.13180 versus true signed_reverse 0.13164 and unsigned reverse 0.13265"

lowRankCompressionExecuted : SenderCompressionGateState
lowRankCompressionExecuted = sender-compression-gate-state lowRankCompressionExecutedGate true
  "R=S/D truncated-SVD ladder ranks 1..8 executed with zero support retained"

senderAssignmentDiscriminator : SenderCompressionGateState
senderAssignmentDiscriminator = sender-compression-gate-state senderAssignmentDiscriminatorGate true
  "preceding sender-pattern permutation discriminator: p=0.0198, one of 100 permutations outperformed the real anatomical sender assignment"

polaritySpecificity : SenderCompressionGateState
polaritySpecificity = sender-compression-gate-state polaritySpecificityGate false
  "signed_reverse 0.13164 versus magnitude-only 0.13175 is a small observed gap without a dedicated polarity null/significance receipt"

targetSpecificRatioDispensability : SenderCompressionGateState
targetSpecificRatioDispensability = sender-compression-gate-state targetSpecificRatioDispensabilityGate false
  "sender-scalar compression retains most predictive advantage for this candidate family, but target-specific ratio structure is not proved dispensable for every consumer/session"

receptorResolvedMechanism : SenderCompressionGateState
receptorResolvedMechanism = sender-compression-gate-state receptorResolvedMechanismGate false
  "benchmark sign convention is transmitter-class based and explicitly not receptor-resolved physiology"

independentReplication : SenderCompressionGateState
independentReplication = sender-compression-gate-state independentReplicationGate false
  "single Gauthey recording 04032024_6f_a2_r5"

populationGeneralization : SenderCompressionGateState
populationGeneralization = sender-compression-gate-state populationGeneralizationGate false
  "requires remaining trials/animals and same-object registration/source receipts"

------------------------------------------------------------------------
-- Ibrahim traversal / source graph.
------------------------------------------------------------------------

senderScalarCoordinate : Traversal.DashiKnowledgeCoordinate
senderScalarCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Reasoning/FibreRoutingMaleCNSSenderScalarCompressionSnowballExact.agda"
  "MaleCNS sender-scalar and low-rank signed-fibre compression frontier"
  "570.000 / 612.8 neuroscience candidate"
  "Q130888 Drosophila; Q162657 neurotransmitter; Q180623 acetylcholine; Q210021 GABA; local empirical carrier has no external QID"
  "dashiBRAIN:malecns_signed_fibre_compression.json@817689a1b0b2403513fdcd329ba8f264551a091d"

anatomySourceCoordinate : Traversal.DashiKnowledgeCoordinate
anatomySourceCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Biology/DrosophilaSignedFibreAnatomySourceSnowballExact.agda"
  "signed-fibre transmitter/anatomy primary-source snowball"
  "612.8; acetylcholine 612.8042; unresolved narrower GABA coordinate"
  "Q130888; Q162657; Q180623; Q210021"
  "Eckstein 10.1016/j.cell.2024.03.016; Barnstedt 10.1016/j.neuron.2016.02.015; Yasuyama 10.1002/cne.10867; Xie 10.7554/eLife.25328"

previousCompressionCoordinate : Traversal.DashiKnowledgeCoordinate
previousCompressionCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Reasoning/FibreRoutingMaleCNSCompressionEmpiricalSnowballExact.agda"
  "8-to-1 MaleCNS fibre compression frontier"
  "570.000 / 612.8 neuroscience candidate"
  "local empirical carrier; no external QID"
  "dashiBRAIN:malecns_fibre_compression_ladder.json"

senderScalarDependsOnPreviousCompression : Traversal.DashiFirstLinkEdge
senderScalarDependsOnPreviousCompression = Traversal.dashi-first-link-edge
  senderScalarCoordinate previousCompressionCoordinate Traversal.dependsOn
  Traversal.canonicalDashiFirstLinkPolicy
  "the second-stage compression is only posed after nested selection identifies signed_reverse as the stable one-fibre carrier"
  true

senderScalarSupportedByAnatomySources : Traversal.DashiFirstLinkEdge
senderScalarSupportedByAnatomySources = Traversal.dashi-first-link-edge
  senderScalarCoordinate anatomySourceCoordinate Traversal.supportedBy
  Traversal.canonicalDashiFirstLinkPolicy
  "primary transmitter/anatomy literature bounds interpretation of the local scalar field; it does not manufacture same-object validation"
  true

------------------------------------------------------------------------
-- Cross-pollination boundaries.
------------------------------------------------------------------------

compressionBoundary : Ladder.FibreCompressionLadderBoundary
compressionBoundary = Ladder.canonicalFibreCompressionLadderBoundary

ibrahimBoundary : Ibrahim.FibreCompressionIbrahimSnowballBoundary
ibrahimBoundary = Ibrahim.canonicalFibreCompressionIbrahimSnowballBoundary

causalBoundary : Causal.FibreSufficiencyCausalInterventionBoundary
causalBoundary = Causal.canonicalFibreSufficiencyCausalInterventionBoundary

anatomyBoundary : Anatomy.SignedFibreAnatomySourceBoundary
anatomyBoundary = Anatomy.canonicalSignedFibreAnatomySourceBoundary

record MaleCNSSenderScalarSnowballBoundary : Set where
  constructor malecns-sender-scalar-snowball-boundary
  field
    matrixToSenderScalarCompressionObserved : Bool
    senderPatternAssignmentDiscriminatorPaid : Bool
    polarityMechanismPaid : Bool
    regionalScalarEqualsLiteratureTransmitterFraction : Bool
    senderScalarIsReceptorResolvedExcitationInhibition : Bool
    bestLowRankResidualProvesBiologicalLatentDimension : Bool
    observationalCompressionImpliesCausalSufficiency : Bool
    qidDeweyDoiLinkCreatesEmpiricalAuthority : Bool
    literatureContextMayGuideNextDiscriminator : Bool
    independentReplicationStillRequired : Bool
    earlierNegativeNullsRemainAppendOnly : Bool
open MaleCNSSenderScalarSnowballBoundary public

canonicalMaleCNSSenderScalarSnowballBoundary : MaleCNSSenderScalarSnowballBoundary
canonicalMaleCNSSenderScalarSnowballBoundary = malecns-sender-scalar-snowball-boundary
  true true false false false false false false true true true
