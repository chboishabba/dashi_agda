module DASHI.Physics.Foundations.CausalTransport2026SourceAtlasExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- 2026 CAUSAL-TRANSPORT SOURCE ATLAS
--
-- Source-owned experimental/theoretical results relevant to the causal-
-- transport hierarchy.  Quantum teleportation, quantum-energy teleportation,
-- mathematical wormholes and FTL are intentionally kept as different claims.
------------------------------------------------------------------------

record CausalTransportSource : Set where
  constructor causal-transport-source
  field
    doi : String
    sourceRole : String
    resultClass : String
    physicalExperiment : Bool
    literalMatterTransport : Bool
    causalSuperluminalTransport : Bool

open CausalTransportSource public

iulianoEtAl2026 : CausalTransportSource
iulianoEtAl2026 =
  causal-transport-source
    "10.1038/s41467-026-72818-6"
    "unconditional teleported CNOT between remote diamond-based solid-state qubit registers"
    "remote entanglement + local logic + mid-circuit measurement + real-time classical feed-forward"
    true false false

pengEtAl2026 : CausalTransportSource
pengEtAl2026 =
  causal-transport-source
    "10.1038/s41567-026-03348-7"
    "teleportation-based single-photon transmission through a lossy channel with higher efficiency than direct transmission through that channel"
    "experimental quantum-communication advantage; not superluminal signalling"
    true false false

dolevIkedaOz2026 : CausalTransportSource
dolevIkedaOz2026 =
  causal-transport-source
    "10.1103/7s7y-7xcn"
    "quantum-energy-teleportation-based quantum key distribution protocol"
    "QET theory using entanglement, local operations and classical communication; no physical particle/energy carrier is sent between parties"
    false false false

liLiuLu2026 : CausalTransportSource
liLiuLu2026 =
  causal-transport-source
    "10.1103/9h7h-686p"
    "Einstein gravity coupled to a massless phantom scalar; wormhole/black-hole solution family including negative-mass black holes"
    "mathematical alternative-gravity/exotic-matter solution"
    false false false

mehdizadehZiaie2026 : CausalTransportSource
mehdizadehZiaie2026 =
  causal-transport-source
    "10.1016/j.nuclphysb.2026.117555"
    "Casimir-supported traversable wormhole solutions in Einstein-Gauss-Bonnet gravity with energy-condition/stability analysis"
    "mathematical modified-gravity solution"
    false false false

record CausalTransport2026SourceAtlas : Set where
  constructor causal-transport-2026-source-atlas
  field
    unconditionalRemoteGateTeleportationExperimentPaid : Bool
    classicalFeedForwardRequiredByExperiment : Bool
    remoteEntanglementRequiredByExperiment : Bool
    lossyChannelTeleportationAdvantageExperimentPaid : Bool
    quantumTeleportationCountsAsFTL : Bool
    quantumGateTeleportationCountsAsMatterTransport : Bool
    teleportationTransmissionAdvantageCountsAsFTL : Bool
    qetCarrierFreeProtocolTheorySourcePaid : Bool
    qetUsesClassicalCommunication : Bool
    qetCountsAsFTL : Bool
    qetCountsAsMacroscopicPropellantlessEnergyTransport : Bool
    phantomScalarWormholeNegativeMassTheorySourcePaid : Bool
    casimirEGBTraversableWormholeTheorySourcePaid : Bool
    mathematicalWormholeSolutionCountsAsPhysicalWormhole : Bool
    modifiedGravitySolutionCountsAsStandardGRSource : Bool
    physicalWormholeBuilt : Bool
    causalShortcutMeasured : Bool

open CausalTransport2026SourceAtlas public

canonicalCausalTransport2026SourceAtlas : CausalTransport2026SourceAtlas
canonicalCausalTransport2026SourceAtlas =
  causal-transport-2026-source-atlas
    true true true true
    false false false
    true true false false
    true true
    false false false false

record CausalTransport2026AttributionBoundary : Set where
  constructor causal-transport-2026-attribution-boundary
  field
    iulianoEtAlOwnRemoteGateTeleportationExperiment : Bool
    pengEtAlOwnLossyChannelTeleportationAdvantageExperiment : Bool
    dolevIkedaOzOwnQETQKDProtocol : Bool
    liLiuLuOwnPhantomScalarSolutionFamily : Bool
    mehdizadehZiaieOwnCasimirEGBWormholeSolutions : Bool
    dashiOwnsTypedSeparationAndNonPromotion : Bool
    crossSourceCompositionTransfersNoMechanismOrExperimentalAuthority : Bool

open CausalTransport2026AttributionBoundary public

canonicalCausalTransport2026AttributionBoundary : CausalTransport2026AttributionBoundary
canonicalCausalTransport2026AttributionBoundary =
  causal-transport-2026-attribution-boundary true true true true true true true
