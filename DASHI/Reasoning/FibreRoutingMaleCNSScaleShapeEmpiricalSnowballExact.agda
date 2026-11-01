module DASHI.Reasoning.FibreRoutingMaleCNSScaleShapeEmpiricalSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.FibreRoutingMaleCNSSenderScalarCompressionSnowballExact as Sender
import DASHI.Reasoning.FibreRoutingCompressionLadderExact as Ladder
import DASHI.Reasoning.FibreRoutingCompressionIbrahimSnowballExact as Ibrahim
import DASHI.Reasoning.FibreRoutingSufficiencyCausalInterventionSnowballExact as Causal
import DASHI.Biology.DrosophilaJoinedObserverSourceSnowballExact as Source
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal

------------------------------------------------------------------------
-- REAL MALECNS SCALE / RELATIVE-SHAPE DISCRIMINATOR
--
-- Exact runtime decomposition:
--   D_ij = sOut_i * P_ij
--   S_ij = sOut_i * P_ij * R_ij
--
-- D is already a membership-mass-normalized regional coupling carrier, not a
-- raw synapse-count matrix.  The current regression also standardizes candidate
-- features inside each training fold, so global scalar rescaling is not the
-- scientific question here.  The useful decomposition is sender scale versus
-- relative target shape versus signed modulation.
------------------------------------------------------------------------

data NetworkCoordinate : Set where
  senderScaleCoordinate : NetworkCoordinate
  relativeTargetShapeCoordinate : NetworkCoordinate
  signedModulationCoordinate : NetworkCoordinate

record FactorizedNetworkCarrier : Set where
  constructor factorized-network-carrier
  field
    scaleMeaning : String
    shapeMeaning : String
    signedMeaning : String
    recompositionD : String
    recompositionS : String
open FactorizedNetworkCarrier public

canonicalFactorizedCarrier : FactorizedNetworkCarrier
canonicalFactorizedCarrier = factorized-network-carrier
  "sOut_i = sum_j |D_ij|; sender-level density-like coupling scale"
  "P_ij = D_ij / sOut_i; row-relative target distribution / wiring shape"
  "R_ij = S_ij / D_ij on non-zero D support; relative signed/transmitter modulation"
  "D_ij = sOut_i * P_ij"
  "S_ij = sOut_i * P_ij * R_ij"

record ScaleShapeRuntimeReceipt : Set where
  constructor scale-shape-runtime-receipt
  field
    repository : String
    branch : String
    runtimeCommit : String
    artifactPath : String
    trialIdentity : String
    testReceipt : String
    regionCount : Nat
    exactDReconstructionError : String
    exactSReconstructionError : String
    signedReverseResidual : String
    relativeSignedShapeResidual : String
    relativeUnsignedShapeResidual : String
    absoluteDensityLikeResidual : String
    senderStrengthOnlyResidual : String
    signedVsRelativeSignedGap : String
    unsignedShapeVsAbsoluteGap : String
    shapeVsStrengthOnlyGap : String
    scientificBoundary : String
open ScaleShapeRuntimeReceipt public

currentScaleShapeRuntime : ScaleShapeRuntimeReceipt
currentScaleShapeRuntime = scale-shape-runtime-receipt
  "github.com/chboishabba/dashiBRAIN"
  "agent/malecns-real-benchmark-tranche"
  "707cde7e46c9641c826e53eae56c4b36951e67d5"
  "data/gauthey_lbm/jrc2018_regions_a2_r5/malecns_network_scale_shape.json"
  "04032024_6f_a2_r5"
  "179/179 full pytest suite; 9/9 focused scale/shape and discriminator tests"
  26
  "< 6e-17"
  "< 6e-17"
  "0.13164"
  "0.13173"
  "0.13253"
  "0.13265"
  "0.13404"
  "+0.00009"
  "-0.00012 for P relative to D"
  "-0.00151 for P relative to strength-only"
  "For this one joined-controlled LORO consumer, relative wiring shape carries materially more transferable information than sender strength alone, and removing sender scale from the signed carrier changes residual only by 9e-5. This does not prove absolute scale is biologically irrelevant for other physical, energetic, developmental, or intervention consumers."

------------------------------------------------------------------------
-- Consumer-indexed interpretations.
------------------------------------------------------------------------

data NetworkConsumer : Set where
  joinedFunctionalTransferConsumer : NetworkConsumer
  physicalCapacityConsumer : NetworkConsumer
  topologyShapeConsumer : NetworkConsumer
  signedFunctionalConsumer : NetworkConsumer
  interventionConsumer : NetworkConsumer

record CoordinateRequirement : Set where
  constructor coordinate-requirement
  field
    consumer : NetworkConsumer
    scaleRequiredByPresentEvidence : Bool
    shapeRequiredByPresentEvidence : Bool
    signedModulationRequiredByPresentEvidence : Bool
    interpretation : String
open CoordinateRequirement public

joinedFunctionalRequirement : CoordinateRequirement
joinedFunctionalRequirement = coordinate-requirement
  joinedFunctionalTransferConsumer false true true
  "Current session: P*R nearly matches full S, while strength-only performs worst. This is an empirical present-consumer reading, not universal sufficiency."

physicalCapacityRequirement : CoordinateRequirement
physicalCapacityRequirement = coordinate-requirement
  physicalCapacityConsumer true false false
  "Physical/energetic capacity questions may depend on total coupling scale even where the present normalized functional-transfer consumer does not."

topologyShapeRequirement : CoordinateRequirement
topologyShapeRequirement = coordinate-requirement
  topologyShapeConsumer false true false
  "A normalized routing/topology consumer may quotient out sender scale while retaining target-distribution shape."

signedFunctionalRequirement : CoordinateRequirement
signedFunctionalRequirement = coordinate-requirement
  signedFunctionalConsumer false true true
  "The current functional-transfer result favours relative shape plus signed modulation over unsigned shape, but dedicated polarity and replication gates remain separate."

interventionRequirement : CoordinateRequirement
interventionRequirement = coordinate-requirement
  interventionConsumer false false false
  "Observational compression does not establish which coordinates suffice under intervention; no requirement is promoted here before intervention-compatible evidence."

------------------------------------------------------------------------
-- Promotion gates.
------------------------------------------------------------------------

data ScaleShapeGate : Set where
  exactFactorizationGate : ScaleShapeGate
  relativeSignedNearFullGate : ScaleShapeGate
  relativeUnsignedBeatsAbsoluteGate : ScaleShapeGate
  shapeBeatsStrengthOnlyGate : ScaleShapeGate
  globalScaleIrrelevanceGate : ScaleShapeGate
  allPhysicalConsumersScaleFreeGate : ScaleShapeGate
  polarityMechanismGate : ScaleShapeGate
  interventionSufficiencyGate : ScaleShapeGate
  independentReplicationGate : ScaleShapeGate

record ScaleShapeGateState : Set where
  constructor scale-shape-gate-state
  field
    gate : ScaleShapeGate
    paid : Bool
    evidenceReference : String
open ScaleShapeGateState public

exactFactorization : ScaleShapeGateState
exactFactorization = scale-shape-gate-state exactFactorizationGate true
  "runtime reconstruction errors for D=sOut*P and S=sOut*P*R were both below 6e-17"

relativeSignedNearFull : ScaleShapeGateState
relativeSignedNearFull = scale-shape-gate-state relativeSignedNearFullGate true
  "P*R reverse residual 0.13173 versus full S reverse 0.13164; observed gap 0.00009"

relativeUnsignedBeatsAbsolute : ScaleShapeGateState
relativeUnsignedBeatsAbsolute = scale-shape-gate-state relativeUnsignedBeatsAbsoluteGate true
  "P reverse residual 0.13253 versus D reverse 0.13265 on the same joined-controlled consumer"

shapeBeatsStrengthOnly : ScaleShapeGateState
shapeBeatsStrengthOnly = scale-shape-gate-state shapeBeatsStrengthOnlyGate true
  "P reverse residual 0.13253 versus sender-strength-only 0.13404; target-routing shape materially improves held-out prediction"

globalScaleIrrelevance : ScaleShapeGateState
globalScaleIrrelevance = scale-shape-gate-state globalScaleIrrelevanceGate false
  "present feature standardization and one consumer make a universal global-scale claim inappropriate"

allPhysicalConsumersScaleFree : ScaleShapeGateState
allPhysicalConsumersScaleFree = scale-shape-gate-state allPhysicalConsumersScaleFreeGate false
  "capacity, energetic, developmental and other physical consumers may require absolute/density-like scale"

polarityMechanism : ScaleShapeGateState
polarityMechanism = scale-shape-gate-state polarityMechanismGate false
  "relative signed shape beats unsigned shape, but prior dedicated polarity-significance gate remains unpaid"

interventionSufficiency : ScaleShapeGateState
interventionSufficiency = scale-shape-gate-state interventionSufficiencyGate false
  "observational LORO equivalence does not establish intervention-preserving equivalence"

independentReplication : ScaleShapeGateState
independentReplication = scale-shape-gate-state independentReplicationGate false
  "single Gauthey recording 04032024_6f_a2_r5"

------------------------------------------------------------------------
-- Ibrahim traversal / attribution coordinates.
------------------------------------------------------------------------

scaleShapeCoordinate : Traversal.DashiKnowledgeCoordinate
scaleShapeCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Reasoning/FibreRoutingMaleCNSScaleShapeEmpiricalSnowballExact.agda"
  "MaleCNS scale / relative-shape / signed-modulation empirical frontier"
  "570.000 / 612.8 neuroscience candidate"
  "local empirical carrier has no external QID; concept QIDs and source QIDs remain separate metadata"
  "dashiBRAIN:malecns_network_scale_shape.json@707cde7e46c9641c826e53eae56c4b36951e67d5"

senderScalarCoordinate : Traversal.DashiKnowledgeCoordinate
senderScalarCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Reasoning/FibreRoutingMaleCNSSenderScalarCompressionSnowballExact.agda"
  "sender-scalar and low-rank signed-fibre compression frontier"
  "570.000 / 612.8 neuroscience candidate"
  "Q130888; Q162657; Q180623; Q210021 are external identity coordinates only"
  "MaleCNS/Gauthey/BIFROST/VFB/JRC2018 source chain plus dashiBRAIN signed-compression receipt"

ibrahimCompressionCoordinate : Traversal.DashiKnowledgeCoordinate
ibrahimCompressionCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Reasoning/FibreRoutingCompressionIbrahimSnowballExact.agda"
  "consumer-relative compression / MDL / MoE / grokking attribution atlas"
  "006.31 machine learning; 005.746 data compression; narrower technique Dewey coordinates remain explicit"
  "Q2539; Q2493; Q1417790; Q30688561; Q126362531; unresolved exact technique QIDs retained"
  "Ibrahim method DOI 10.1016/j.jocs.2016.12.001; Rissanen 10.1016/0005-1098(78)90005-5; Jacobs 10.1162/neco.1991.3.1.79; canonical arXiv identities retained for later ML techniques"

scaleShapeDependsOnSenderCompression : Traversal.DashiFirstLinkEdge
scaleShapeDependsOnSenderCompression = Traversal.dashi-first-link-edge
  scaleShapeCoordinate senderScalarCoordinate Traversal.dependsOn
  Traversal.canonicalDashiFirstLinkPolicy
  "relative-vs-absolute decomposition follows the winning signed_reverse/sender-scalar compression frontier and keeps the same joined-controlled consumer"
  true

scaleShapeCrossPollinatesWithCompressionTheory : Traversal.DashiFirstLinkEdge
scaleShapeCrossPollinatesWithCompressionTheory = Traversal.dashi-first-link-edge
  scaleShapeCoordinate ibrahimCompressionCoordinate Traversal.crossPollinatesWith
  Traversal.canonicalDashiFirstLinkPolicy
  "scale removal is another consumer-indexed compression/quotient; metadata or analogy does not establish universal equivalence"
  true

------------------------------------------------------------------------
-- Existing source and causal boundaries reused rather than forked.
------------------------------------------------------------------------

sourceBoundary : Source.SourceSnowballBoundary
sourceBoundary = Source.canonicalSourceSnowballBoundary

senderBoundary : Sender.MaleCNSSenderScalarSnowballBoundary
senderBoundary = Sender.canonicalMaleCNSSenderScalarSnowballBoundary

compressionBoundary : Ladder.FibreCompressionLadderBoundary
compressionBoundary = Ladder.canonicalFibreCompressionLadderBoundary

ibrahimBoundary : Ibrahim.FibreCompressionIbrahimSnowballBoundary
ibrahimBoundary = Ibrahim.canonicalFibreCompressionIbrahimSnowballBoundary

causalBoundary : Causal.FibreSufficiencyCausalInterventionBoundary
causalBoundary = Causal.canonicalFibreSufficiencyCausalInterventionBoundary

record MaleCNSScaleShapeBoundary : Set where
  constructor malecns-scale-shape-boundary
  field
    scaleShapeSignedCoordinatesRemainSeparate : Bool
    presentFunctionalConsumerMayQuotientSenderScale : Bool
    presentFunctionalConsumerMayEraseTargetShape : Bool
    relativeSignedNearFullObserved : Bool
    relativeSimilarityEqualsAbsolutePhysicalIdentity : Bool
    topologySimilarityEqualsSignedSimilarity : Bool
    observationalEquivalenceImpliesInterventionEquivalence : Bool
    deweyQidDoiLinkCreateEmpiricalPayment : Bool
    primarySourceAndRuntimeRolesRemainSeparate : Bool
    independentReplicationStillRequired : Bool
    presentResultClaimedUniversal : Bool
open MaleCNSScaleShapeBoundary public

canonicalMaleCNSScaleShapeBoundary : MaleCNSScaleShapeBoundary
canonicalMaleCNSScaleShapeBoundary = malecns-scale-shape-boundary
  true true false true false false false false true true false
