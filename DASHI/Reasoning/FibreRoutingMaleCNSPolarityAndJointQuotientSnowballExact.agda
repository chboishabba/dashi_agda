module DASHI.Reasoning.FibreRoutingMaleCNSPolarityAndJointQuotientSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Reasoning.FibreRoutingMaleCNSSenderScalarCompressionSnowballExact as Sender
import DASHI.Reasoning.FibreRoutingMaleCNSScaleShapeEmpiricalSnowballExact as ScaleShape
import DASHI.Reasoning.FibreRoutingJoinedObserverAdequacyExact as Joined
import DASHI.Reasoning.FibreRoutingSufficiencyCausalInterventionSnowballExact as Causal
import DASHI.Reasoning.FibreRoutingCompressionIbrahimSnowballExact as Ibrahim
import DASHI.Biology.DrosophilaSignedFibreAnatomySourceSnowballExact as Anatomy
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal

------------------------------------------------------------------------
-- EXACT SENDER-POLARITY NULL + JOINT-QUOTIENT FRONTIER
--
-- The polarity experiment acts on the already-compressed sender-scalar field:
--   a_i = m_i z_i,  m_i = |a_i|,  z_i = sign(a_i)
-- and tests m_i z_i D_ij while holding D, |a_i|, the joined functional target,
-- and atlas-overlap control fixed.
--
-- IMPORTANT COMPOSITION BOUNDARY:
-- previous experiments separately support dropping sender scale from S and
-- dropping binary polarity from the sender-scalar carrier.  Those two results
-- do not by themselves certify the composed quotient m_i P_ij.  The repo's
-- existing separate-axis non-promotion theorem is the formal anchor here.
------------------------------------------------------------------------

record PolarityNullReceipt : Set where
  constructor polarity-null-receipt
  field
    repository : String
    branch : String
    runtimeCommit : String
    artifactPath : String
    trialIdentity : String
    testReceipt : String
    regionCount : Nat
    negativeSenderCount : Nat
    exactAssignmentCount : Nat
    assignmentsAtOrBetterThanObserved : Nat
    empiricalP : String
    observedSenderScalarResidual : String
    magnitudeOnlyResidual : String
    polarityGap : String
    nullMinimum : String
    nullMean : String
    nullMedian : String
    nullMaximum : String
    interpretation : String

open PolarityNullReceipt public

currentPolarityNull : PolarityNullReceipt
currentPolarityNull = polarity-null-receipt
  "github.com/chboishabba/dashiBRAIN"
  "agent/malecns-real-benchmark-tranche"
  "a47349d3dd8a728e50751184716c93b8a39c7ffb"
  "data/gauthey_lbm/jrc2018_regions_a2_r5/malecns_sender_scalar_polarity_null.json"
  "04032024_6f_a2_r5"
  "182/182 full pytest suite; 12/12 focused polarity/scale-shape/compression tests"
  26
  1
  26
  7
  "7/26 = 0.2692"
  "0.131796"
  "0.131839"
  "+0.000043"
  "0.131667"
  "0.131917"
  "0.131841"
  "0.133097"
  "For this session and declared joined LORO consumer, the observed single-negative polarity placement is not distinguished by the exhaustive randomization test. This supports retaining sender magnitude/tendency while withholding a polarity-specific mechanism claim."

------------------------------------------------------------------------
-- Promotion state.
------------------------------------------------------------------------

data PolarityGate : Set where
  exactEnumerationExecutedGate : PolarityGate
  signCountPreservedGate : PolarityGate
  senderMagnitudePreservedGate : PolarityGate
  polarityAssignmentSpecificityGate : PolarityGate
  polarityMechanismGate : PolarityGate
  magnitudeOnlyAdequacyGate : PolarityGate
  composedMagnitudeShapeGate : PolarityGate
  independentReplicationGate : PolarityGate

record PolarityGateState : Set where
  constructor polarity-gate-state
  field
    gate : PolarityGate
    paid : Bool
    evidenceReference : String

open PolarityGateState public

exactEnumerationExecuted : PolarityGateState
exactEnumerationExecuted = polarity-gate-state exactEnumerationExecutedGate true
  "all 26 distinct single-negative sender assignments enumerated"

signCountPreserved : PolarityGateState
signCountPreserved = polarity-gate-state signCountPreservedGate true
  "null preserves one negative and 25 positive sender labels"

senderMagnitudePreserved : PolarityGateState
senderMagnitudePreserved = polarity-gate-state senderMagnitudePreservedGate true
  "null permutes polarity placement while holding each sender magnitude |a_i| fixed"

polarityAssignmentSpecificity : PolarityGateState
polarityAssignmentSpecificity = polarity-gate-state polarityAssignmentSpecificityGate false
  "7/26 assignments matched or beat the observed placement; p=0.2692"

polarityMechanism : PolarityGateState
polarityMechanism = polarity-gate-state polarityMechanismGate false
  "non-rejected polarity assignment null cannot establish receptor-resolved or causal sign mechanism"

magnitudeOnlyAdequacy : PolarityGateState
magnitudeOnlyAdequacy = polarity-gate-state magnitudeOnlyAdequacyGate true
  "magnitude-only sender-scalar residual 0.131839 is extremely close to observed signed-scalar residual 0.131796 for this consumer"

composedMagnitudeShape : PolarityGateState
composedMagnitudeShape = polarity-gate-state composedMagnitudeShapeGate false
  "m_i P_ij has not yet been executed directly; separate evidence for dropping absolute scale and dropping polarity may not be composed automatically"

independentReplication : PolarityGateState
independentReplication = polarity-gate-state independentReplicationGate false
  "single Gauthey recording 04032024_6f_a2_r5"

------------------------------------------------------------------------
-- Existing theorem anchor: separate-axis sufficiency does not auto-promote to
-- sufficiency after jointly erasing both axes.
------------------------------------------------------------------------

separateAxisAdequacyDoesNotPayJointQuotient :
  NonFactor.SeparateAxisSufficiencyImpliesIntersectionalSufficiencyPermission → ⊥
separateAxisAdequacyDoesNotPayJointQuotient =
  Joined.intersectionalNoAutoPromotionAnchor

------------------------------------------------------------------------
-- Ibrahim traversal / attribution coordinates.
------------------------------------------------------------------------

polarityCoordinate : Traversal.DashiKnowledgeCoordinate
polarityCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Reasoning/FibreRoutingMaleCNSPolarityAndJointQuotientSnowballExact.agda"
  "MaleCNS exact sender-polarity randomization and joint-quotient frontier"
  "570.000 / 612.8 neuroscience candidate"
  "Q130888 Drosophila; Q162657 neurotransmitter; local empirical receipt has no external QID"
  "dashiBRAIN:malecns_sender_scalar_polarity_null.json@a47349d3dd8a728e50751184716c93b8a39c7ffb"

senderCoordinate : Traversal.DashiKnowledgeCoordinate
senderCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Reasoning/FibreRoutingMaleCNSSenderScalarCompressionSnowballExact.agda"
  "sender-scalar / low-rank signed-fibre frontier"
  "570.000 / 612.8 neuroscience candidate"
  "Q130888; Q162657; Q180623; Q210021"
  "dashiBRAIN:malecns_signed_fibre_compression.json"

scaleShapeCoordinate : Traversal.DashiKnowledgeCoordinate
scaleShapeCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Reasoning/FibreRoutingMaleCNSScaleShapeEmpiricalSnowballExact.agda"
  "absolute-scale / relative-shape / signed-modulation frontier"
  "570.000 / 612.8 neuroscience candidate"
  "local empirical carrier; no external QID"
  "dashiBRAIN:malecns_network_scale_shape.json"

polarityDependsOnSenderCompression : Traversal.DashiFirstLinkEdge
polarityDependsOnSenderCompression = Traversal.dashi-first-link-edge
  polarityCoordinate senderCoordinate Traversal.dependsOn
  Traversal.canonicalDashiFirstLinkPolicy
  "the polarity null is defined only after the signed matrix is compressed to sender tendencies a_i"
  true

jointQuotientDependsOnScaleShape : Traversal.DashiFirstLinkEdge
jointQuotientDependsOnScaleShape = Traversal.dashi-first-link-edge
  polarityCoordinate scaleShapeCoordinate Traversal.dependsOn
  Traversal.canonicalDashiFirstLinkPolicy
  "the proposed m_i P_ij quotient jointly removes absolute sender scale and binary polarity and therefore requires a direct composed-consumer test"
  true

------------------------------------------------------------------------
-- Reused boundaries.
------------------------------------------------------------------------

senderBoundary : Sender.MaleCNSSenderScalarSnowballBoundary
senderBoundary = Sender.canonicalMaleCNSSenderScalarSnowballBoundary

scaleShapeBoundary : ScaleShape.MaleCNSScaleShapeBoundary
scaleShapeBoundary = ScaleShape.canonicalMaleCNSScaleShapeBoundary

causalBoundary : Causal.FibreSufficiencyCausalInterventionBoundary
causalBoundary = Causal.canonicalFibreSufficiencyCausalInterventionBoundary

ibrahimBoundary : Ibrahim.FibreCompressionIbrahimSnowballBoundary
ibrahimBoundary = Ibrahim.canonicalFibreCompressionIbrahimSnowballBoundary

anatomyBoundary : Anatomy.SignedFibreAnatomySourceBoundary
anatomyBoundary = Anatomy.canonicalSignedFibreAnatomySourceBoundary

record PolarityJointQuotientBoundary : Set where
  constructor polarity-joint-quotient-boundary
  field
    exhaustivePolarityNullExecuted : Bool
    observedPolarityAssignmentDistinguished : Bool
    magnitudeProfileRetainedAsUsefulCoordinate : Bool
    dropScaleAndDropPolaritySeparatelyImpliesJointDrop : Bool
    mTimesPDirectExecutionStillRequired : Bool
    nonRejectedPolarityNullMayBeRewrittenAsPolarityMechanism : Bool
    qidDeweyDoiLinkCreateEmpiricalPayment : Bool
    independentReplicationStillRequired : Bool
    negativePolarityResultRemainsAppendOnly : Bool

open PolarityJointQuotientBoundary public

canonicalPolarityJointQuotientBoundary : PolarityJointQuotientBoundary
canonicalPolarityJointQuotientBoundary = polarity-joint-quotient-boundary
  true false true false true false false true true
