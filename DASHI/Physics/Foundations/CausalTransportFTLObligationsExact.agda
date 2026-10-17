{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CausalTransportFTLObligationsExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.QuantumStressEnergyEngineeringBridgeExact as QuantumStress

------------------------------------------------------------------------
-- CAUSAL TRANSPORT / FTL OBLIGATION HIERARCHY
--
-- Science-fiction motifs are candidate consumers only.  This module gives
-- them typed scientific obligations without granting evidence or authority.
------------------------------------------------------------------------

data VelocityObservable : Set where
  phaseVelocity : VelocityObservable
  groupVelocity : VelocityObservable
  pulsePeakVelocity : VelocityObservable
  tunnellingOrInterferenceTime : VelocityObservable
  signalFrontVelocity : VelocityObservable

data TeleportationKind : Set where
  stateTeleportation : TeleportationKind
  gateTeleportation : TeleportationKind
  quantumEnergyTeleportation : TeleportationKind
  carrierMatterTransport : TeleportationKind
  causalSignalTransport : TeleportationKind

record SuperluminalityObserverBoundary : Set where
  constructor superluminality-observer-boundary
  field
    phaseVelocityDistinctFromSignalFront : Bool
    groupVelocityDistinctFromSignalFront : Bool
    pulsePeakDistinctFromSignalFront : Bool
    tunnellingTimeDistinctFromSignalFront : Bool
    superluminalPeakDoesNotImplySuperluminalSignal : Bool

open SuperluminalityObserverBoundary public

canonicalSuperluminalityObserverBoundary : SuperluminalityObserverBoundary
canonicalSuperluminalityObserverBoundary =
  superluminality-observer-boundary true true true true true

record QuantumTeleportationCausalityBoundary : Set where
  constructor quantum-teleportation-causality-boundary
  field
    stateTeleportationDistinctFromCarrierTransport : Bool
    gateTeleportationDistinctFromCarrierTransport : Bool
    quantumEnergyTeleportationDistinctFromMatterTransport : Bool
    classicalCommunicationDependenceRemainsExplicit : Bool
    quantumTeleportationDoesNotImplyMatterTransport : Bool
    quantumTeleportationDoesNotImplyFTLSignalling : Bool

open QuantumTeleportationCausalityBoundary public

canonicalQuantumTeleportationBoundary : QuantumTeleportationCausalityBoundary
canonicalQuantumTeleportationBoundary =
  quantum-teleportation-causality-boundary true true true true true true

record AnalogueSpacetimeNonPromotion : Set where
  constructor analogue-spacetime-non-promotion
  field
    analogueModelReference : String
    simulatorOrMaterialReference : String
    literalSpacetimeObservablePaid : Bool
    analogueDoesNotPromoteLiteralMetricEngineering : Bool

open AnalogueSpacetimeNonPromotion public

canonicalAnalogueSpacetimeNonPromotion : AnalogueSpacetimeNonPromotion
canonicalAnalogueSpacetimeNonPromotion =
  analogue-spacetime-non-promotion
    "analogue/synthetic spacetime object"
    "material/simulator realization"
    false true

record WarpMetricStressEnergyObligations : Set where
  constructor warp-metric-stress-energy-obligations
  field
    metricOrADMDataReference : String
    requiredStressEnergyReference : String
    localEnergyConditionReference : String
    averagedOrQuantumAdmissibilityReference : String
    horizonReference : String
    tidalFieldReference : String
    stabilityBackreactionReference : String
    chronologyReference : String
    physicalSourceSameObjectPaid : Bool
    superluminalTransportPaid : Bool

open WarpMetricStressEnergyObligations public

canonicalWarpMetricObligations : WarpMetricStressEnergyObligations
canonicalWarpMetricObligations =
  warp-metric-stress-energy-obligations
    "literal metric/ADM data required"
    "derive T_mu_nu from selected geometry"
    "NEC/WEC/DEC status"
    "ANEC/QEI/quantum-source obligation"
    "horizon analysis"
    "tidal-field analysis"
    "stability/backreaction analysis"
    "chronology/CTC analysis"
    false false

record TraversableWormholeEngineeringObligations : Set where
  constructor traversable-wormhole-engineering-obligations
  field
    literalMetricAndTopologyReference : String
    throatAndTraversabilityReference : String
    stressEnergySourceReference : String
    energyConditionAndQuantumStatusReference : String
    tidalConstraintReference : String
    stabilityBackreactionReference : String
    chronologyReference : String
    physicalSourceSameObjectPaid : Bool
    traversalExperimentPaid : Bool

open TraversableWormholeEngineeringObligations public

canonicalTraversableWormholeObligations : TraversableWormholeEngineeringObligations
canonicalTraversableWormholeObligations =
  traversable-wormhole-engineering-obligations
    "literal metric/topology required"
    "throat/traversability required"
    "source T_mu_nu required"
    "energy-condition/QEI status required"
    "tidal constraints required"
    "stability/backreaction required"
    "causal/chronology status required"
    false false

------------------------------------------------------------------------
-- Strongest target: an obligation record can be present while unpaid.  Actual
-- promotion requires a separate proof-carrying witness that every required
-- receipt in the candidate is true.  Stress-energy source evidence is
-- conditional: it is mandatory only for candidates that claim literal metric
-- engineering, not for a hypothetical non-metric causal-transport mechanism.
------------------------------------------------------------------------

record CausalSuperluminalTransportPromotion : Set where
  constructor causal-superluminal-transport-promotion
  field
    endpointAReference : String
    endpointBReference : String
    controllableInformationOrMatterTransport : Bool
    spacelikeSeparationReceipt : Bool
    independentEndpointClockReceipt : Bool
    signalFrontOrCausalReceipt : Bool
    metricOrCausalStructureReceipt : Bool
    metricClaimed : Bool
    sourceStressEnergyReceiptIfMetricClaimed : Bool
    chronologyStatusResolved : Bool
    independentReplication : Bool

open CausalSuperluminalTransportPromotion public

canonicalCausalSuperluminalTransportPromotion : CausalSuperluminalTransportPromotion
canonicalCausalSuperluminalTransportPromotion =
  causal-superluminal-transport-promotion
    "endpoint-A" "endpoint-B"
    false false false false false false false false false

record CausalSuperluminalTransportWitness
    (candidate : CausalSuperluminalTransportPromotion) : Set where
  constructor causal-superluminal-transport-witness
  field
    transportReceiptIsTrue :
      controllableInformationOrMatterTransport candidate ≡ true
    spacelikeReceiptIsTrue :
      spacelikeSeparationReceipt candidate ≡ true
    endpointClockReceiptIsTrue :
      independentEndpointClockReceipt candidate ≡ true
    causalReceiptIsTrue :
      signalFrontOrCausalReceipt candidate ≡ true
    metricCausalReceiptIsTrue :
      metricOrCausalStructureReceipt candidate ≡ true
    sourceReceiptIfMetricClaimedIsTrue :
      metricClaimed candidate ≡ true →
      sourceStressEnergyReceiptIfMetricClaimed candidate ≡ true
    chronologyReceiptIsTrue :
      chronologyStatusResolved candidate ≡ true
    replicationReceiptIsTrue :
      independentReplication candidate ≡ true

open CausalSuperluminalTransportWitness public

------------------------------------------------------------------------
-- SCI-FI CONSUMER GENERATOR
------------------------------------------------------------------------

data SciFiConsumer : Set where
  replicator : SciFiConsumer
  transporter : SciFiConsumer
  tractorBeam : SciFiConsumer
  forceField : SciFiConsumer
  inertialDamper : SciFiConsumer
  artificialGravity : SciFiConsumer
  holodeck : SciFiConsumer
  selfHealingSpacecraft : SciFiConsumer
  stargate : SciFiConsumer
  warpDrive : SciFiConsumer
  reactionlessDrive : SciFiConsumer

record SciFiConsumerBoundary : Set where
  constructor scifi-consumer-boundary
  field
    scifiConsumerHasNoScientificAuthority : Bool
    fictionDoesNotPayMechanism : Bool
    fictionDoesNotPayEmpiricalEvidence : Bool
    fictionDoesNotPayEngineeringRealizability : Bool
    candidateConsumerMayStillGenerateTestableObligations : Bool

open SciFiConsumerBoundary public

canonicalSciFiBoundary : SciFiConsumerBoundary
canonicalSciFiBoundary =
  scifi-consumer-boundary true true true true true

record CausalTransportHierarchyBoundary : Set where
  constructor causal-transport-hierarchy-boundary
  field
    apparentSuperluminalityNotFTL : Bool
    teleportationNotFTL : Bool
    analogueSpacetimeNotLiteralSpacetimeEngineering : Bool
    wormholeSolutionNotEngineeringReceipt : Bool
    warpMetricNotPhysicalSource : Bool
    subluminalWarpLikeGeometryNotFTL : Bool
    exoticStressDoesNotSkipQuantumStressLadder : Bool
    causalFTLPromotionRequiresProofCarryingReceipts : Bool

open CausalTransportHierarchyBoundary public

canonicalCausalTransportHierarchyBoundary : CausalTransportHierarchyBoundary
canonicalCausalTransportHierarchyBoundary =
  causal-transport-hierarchy-boundary true true true true true true true true
