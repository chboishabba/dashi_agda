module DASHI.Cognition.Teleodynamics.TeleodynamicsIITPhiBoundaryExact where

------------------------------------------------------------------------
-- TELEODYNAMICS <-> IIT/PHI NON-COLLAPSE / COMPARISON BOUNDARY
--
-- Michels' Principia-II lane and sibling IIT/phi PR #1148 now expose two
-- independently defined integration surfaces.  They are deliberately not
-- identified by shared words such as "integration", "coherence", or
-- "consciousness".
--
-- Local teleodynamics owner:
--   * C_{mu nu}: normalized observable/rate cross-correlation witness;
--   * coherence density A = tr(C^T C) / Frobenius-square surface;
--   * architecture/task cosine-like normalized overlaps;
--   * proposed five-coordinate qualia tuple Q = {Abar,G,R,J,M}.
--
-- Sibling IIT #1148 reports:
--   * finite causal system / TPM and directional partition carrier;
--   * cause/effect probability-loss inputs;
--   * system-phi at a partition as min(cause,effect) intrinsic information;
--   * normalized MIP selection with the returned phi_s unnormalized at MIP;
--   * separate phiSystem / phiDistinction / phiRelation / bigPhi layers;
--   * consumer-relative biological/observer boundaries.
--
-- Cross-branch IIT facts below are receipts, not imported Agda theorem
-- authority.  Any numerical/scientific comparison must supply a SAME-state,
-- SAME-intervention and SAME-consumer bridge plus the IIT partition/repertoire
-- construction.  Matching scalar values alone does not create such a bridge.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.TeleodynamicsPrincipiaTwoExact as Tele

------------------------------------------------------------------------
-- 1. Typed theory/observable levels.
------------------------------------------------------------------------

data TeleodynamicIntegrationSurface : Set where
  cTensorCorrelation : TeleodynamicIntegrationSurface
  coherenceDensity : TeleodynamicIntegrationSurface
  architectureSimilarity : TeleodynamicIntegrationSurface
  qualiaCoordinateTuple : TeleodynamicIntegrationSurface


data IITIntegrationSurface : Set where
  systemPhi : IITIntegrationSurface
  distinctionPhi : IITIntegrationSurface
  relationPhi : IITIntegrationSurface
  bigPhi : IITIntegrationSurface

record IITPhiSiblingReceipt : Set where
  constructor iit-phi-sibling-receipt
  field
    sourcePR : Nat
    finiteCausalCarrierReported : Bool
    directionalPartitionsReported : Bool
    causeEffectLossesReported : Bool
    normalizedMIPReported : Bool
    unnormalizedPhiAtMIPReported : Bool
    systemDistinctionRelationBigPhiSeparated : Bool
    consumerRelativeBiologicalBoundaryReported : Bool
    importedAsLocalKernelTheorem : Bool
open IITPhiSiblingReceipt public

canonicalIITPhiSiblingReceipt : IITPhiSiblingReceipt
canonicalIITPhiSiblingReceipt =
  iit-phi-sibling-receipt
    1148
    true true true true true true true
    false

------------------------------------------------------------------------
-- 2. Same-object comparison contract.
------------------------------------------------------------------------

record TeleodynamicsIITComparisonBridge : Set where
  constructor teleodynamics-iit-comparison-bridge
  field
    sharedUnderlyingStateReceipt : String
    sharedInterventionReceipt : String
    teleodynamicObservableReceipt : String
    IITTPMReceipt : String
    IITDirectionalPartitionReceipt : String
    IITCauseEffectRepertoireReceipt : String
    declaredConsumerReceipt : String
    observationOrDecoderReceipt : String
    heldOutComparisonReceipt : String
    sameUnderlyingStatePaid : Bool
    sameInterventionPaid : Bool
    partitionAndRepertoirePaid : Bool
    sameDeclaredConsumerPaid : Bool
    heldOutComparisonPaid : Bool
open TeleodynamicsIITComparisonBridge public

record TeleodynamicsIITEmpiricalComparison : Set where
  constructor teleodynamics-iit-empirical-comparison
  field
    bridge : TeleodynamicsIITComparisonBridge
    teleodynamicSurface : TeleodynamicIntegrationSurface
    iitSurface : IITIntegrationSurface
    teleodynamicValueLabel : String
    iitValueLabel : String
    associationStatisticLabel : String
    matchedBaselineLabel : String
    falsifierLabel : String
open TeleodynamicsIITEmpiricalComparison public

------------------------------------------------------------------------
-- 3. Authority / non-collapse boundary.
------------------------------------------------------------------------

record TeleodynamicsIITPhiBoundary : Set where
  constructor teleodynamics-iit-phi-boundary
  field
    michelsCoherenceDensityInterfaceLocallyOwned : Bool
    michelsArchitectureOverlapInterfaceLocallyOwned : Bool
    michelsQualiaTupleInterfaceLocallyOwned : Bool
    iitFinitePhiSpineReportedInSibling : Bool

    michelsCoherenceDensityIsIITSystemPhi : Bool
    michelsArchitectureCosineIsIITSystemPhi : Bool
    michelsQualiaCoordinatesAreIITBigPhi : Bool
    equalScalarValuesCreateTheoryIdentity : Bool
    correlationAcrossDatasetsCreatesSameObjectIdentity : Bool

    sharedStateBridgeRequiredForComparison : Bool
    sharedInterventionBridgeRequiredForComparison : Bool
    partitionRepertoireBridgeRequiredForPhiComparison : Bool
    consumerRelativeOutcomeBridgeRequired : Bool
    heldOutComparisonRequired : Bool

    iitSiblingReceiptCreatesLocalKernelTheorem : Bool
    eitherTheoryScoreCreatesConsciousnessIdentity : Bool
    eitherTheoryScoreCreatesPhenomenalIdentity : Bool
    eitherTheoryScoreCreatesMechanismIdentity : Bool
open TeleodynamicsIITPhiBoundary public

canonicalTeleodynamicsIITPhiBoundary : TeleodynamicsIITPhiBoundary
canonicalTeleodynamicsIITPhiBoundary =
  teleodynamics-iit-phi-boundary
    (Tele.coherenceDensityInterfaceDefined Tele.canonicalAuthorityBoundary)
    (Tele.normalizedOverlapInterfaceDefined Tele.canonicalAuthorityBoundary)
    true
    true
    false false false false false
    true true true true true
    false false false false

------------------------------------------------------------------------
-- 4. Explicit impossible promotions.
------------------------------------------------------------------------

data CoherenceDensityCreatesIITSystemPhi : Set where

data QualiaTupleCreatesIITBigPhi : Set where

data EqualScalarCreatesTheoryIdentity : Set where

data IITOrTeleodynamicScoreCreatesPhenomenology : Set where

coherenceDensityDoesNotCreateIITSystemPhi :
  CoherenceDensityCreatesIITSystemPhi → ⊥
coherenceDensityDoesNotCreateIITSystemPhi ()

qualiaTupleDoesNotCreateIITBigPhi :
  QualiaTupleCreatesIITBigPhi → ⊥
qualiaTupleDoesNotCreateIITBigPhi ()

equalScalarDoesNotCreateTheoryIdentity :
  EqualScalarCreatesTheoryIdentity → ⊥
equalScalarDoesNotCreateTheoryIdentity ()

integrationScoreDoesNotCreatePhenomenology :
  IITOrTeleodynamicScoreCreatesPhenomenology → ⊥
integrationScoreDoesNotCreatePhenomenology ()

------------------------------------------------------------------------
-- 5. Productive experimental handoff.
--
-- The useful cross-pollination is comparative, not identificatory: compute both
-- observables on the same declared state/intervention surface, preserve each
-- theory's own construction, then ask whether either/both factor a declared
-- consumer or predict held-out transitions.  This matches the repo-wide
-- consumer-relative sufficiency discipline.
------------------------------------------------------------------------

record ComparativeIntegrationExperimentProtocol : Set where
  constructor comparative-integration-experiment-protocol
  field
    sameStateOrCheckpoint : Bool
    sameIntervention : Bool
    teleodynamicObservablePredeclared : Bool
    iitTPMAndPartitionRulePredeclared : Bool
    iitLevelPredeclared : Bool
    consumerPredeclared : Bool
    matchedBaselineRequired : Bool
    heldOutTransitionRequired : Bool
    comparePredictiveIncrementBeyondEachOther : Bool
    scalarAgreementCountsAsTheoryIdentity : Bool
    eitherScoreCountsAsPhenomenalIdentity : Bool
open ComparativeIntegrationExperimentProtocol public

canonicalComparativeIntegrationExperimentProtocol :
  ComparativeIntegrationExperimentProtocol
canonicalComparativeIntegrationExperimentProtocol =
  comparative-integration-experiment-protocol
    true true true true true true true true true
    false false
