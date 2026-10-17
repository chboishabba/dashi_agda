module DASHI.Physics.Foundations.CausalTransport2026SourceAtlasValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Foundations.CausalTransport2026SourceAtlasExact as S

remote-gate-teleportation-experiment-paid : S.unconditionalRemoteGateTeleportationExperimentPaid S.canonicalCausalTransport2026SourceAtlas ≡ true
remote-gate-teleportation-experiment-paid = refl

classical-feed-forward-is-explicit : S.classicalFeedForwardRequiredByExperiment S.canonicalCausalTransport2026SourceAtlas ≡ true
classical-feed-forward-is-explicit = refl

lossy-channel-teleportation-advantage-paid : S.lossyChannelTeleportationAdvantageExperimentPaid S.canonicalCausalTransport2026SourceAtlas ≡ true
lossy-channel-teleportation-advantage-paid = refl

teleportation-is-not-ftl : S.quantumTeleportationCountsAsFTL S.canonicalCausalTransport2026SourceAtlas ≡ false
teleportation-is-not-ftl = refl

teleportation-advantage-is-not-ftl : S.teleportationTransmissionAdvantageCountsAsFTL S.canonicalCausalTransport2026SourceAtlas ≡ false
teleportation-advantage-is-not-ftl = refl

teleportation-is-not-matter-transport : S.quantumGateTeleportationCountsAsMatterTransport S.canonicalCausalTransport2026SourceAtlas ≡ false
teleportation-is-not-matter-transport = refl

qet-source-paid : S.qetCarrierFreeProtocolTheorySourcePaid S.canonicalCausalTransport2026SourceAtlas ≡ true
qet-source-paid = refl

qet-classical-channel-explicit : S.qetUsesClassicalCommunication S.canonicalCausalTransport2026SourceAtlas ≡ true
qet-classical-channel-explicit = refl

qet-is-not-ftl : S.qetCountsAsFTL S.canonicalCausalTransport2026SourceAtlas ≡ false
qet-is-not-ftl = refl

qet-is-not-macroscopic-propellantless-energy-transport : S.qetCountsAsMacroscopicPropellantlessEnergyTransport S.canonicalCausalTransport2026SourceAtlas ≡ false
qet-is-not-macroscopic-propellantless-energy-transport = refl

wormhole-theory-source-paid : S.phantomScalarWormholeNegativeMassTheorySourcePaid S.canonicalCausalTransport2026SourceAtlas ≡ true
wormhole-theory-source-paid = refl

casimir-modified-gravity-wormhole-source-paid : S.casimirEGBTraversableWormholeTheorySourcePaid S.canonicalCausalTransport2026SourceAtlas ≡ true
casimir-modified-gravity-wormhole-source-paid = refl

wormhole-source-is-not-built-device : S.mathematicalWormholeSolutionCountsAsPhysicalWormhole S.canonicalCausalTransport2026SourceAtlas ≡ false
wormhole-source-is-not-built-device = refl
