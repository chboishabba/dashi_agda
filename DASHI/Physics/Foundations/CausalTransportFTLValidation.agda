{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CausalTransportFTLValidation where

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.Foundations.CausalTransportFTLObligationsExact as FTL

superluminalityBoundaryExists : FTL.SuperluminalityObserverBoundary
superluminalityBoundaryExists = FTL.canonicalSuperluminalityObserverBoundary

teleportationBoundaryExists : FTL.QuantumTeleportationCausalityBoundary
teleportationBoundaryExists = FTL.canonicalQuantumTeleportationBoundary

warpObligationsExist : FTL.WarpMetricStressEnergyObligations
warpObligationsExist = FTL.canonicalWarpMetricObligations

wormholeObligationsExist : FTL.TraversableWormholeEngineeringObligations
wormholeObligationsExist = FTL.canonicalTraversableWormholeObligations

causalFTLRequiresStrongReceipt : FTL.CausalSuperluminalTransportPromotion
causalFTLRequiresStrongReceipt = FTL.canonicalCausalSuperluminalTransportPromotion

peakSpeedDoesNotImplySignalFTL : Bool
peakSpeedDoesNotImplySignalFTL =
  FTL.superluminalPeakDoesNotImplySuperluminalSignal
    FTL.canonicalSuperluminalityObserverBoundary

teleportationDoesNotImplyMatterTransport : Bool
teleportationDoesNotImplyMatterTransport =
  FTL.quantumTeleportationDoesNotImplyMatterTransport
    FTL.canonicalQuantumTeleportationBoundary

scifiHasNoAuthority : Bool
scifiHasNoAuthority = FTL.scifiConsumerHasNoScientificAuthority FTL.canonicalSciFiBoundary
