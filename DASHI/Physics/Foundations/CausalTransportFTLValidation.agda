{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CausalTransportFTLValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Foundations.CausalTransportFTLObligationsExact as FTL

superluminalityBoundaryExists : FTL.SuperluminalityObserverBoundary
superluminalityBoundaryExists = FTL.canonicalSuperluminalityObserverBoundary

teleportationBoundaryExists : FTL.QuantumTeleportationCausalityBoundary
teleportationBoundaryExists = FTL.canonicalQuantumTeleportationBoundary

warpObligationsExist : FTL.WarpMetricStressEnergyObligations
warpObligationsExist = FTL.canonicalWarpMetricObligations

wormholeObligationsExist : FTL.TraversableWormholeEngineeringObligations
wormholeObligationsExist = FTL.canonicalTraversableWormholeObligations

causalFTLObligationsExist : FTL.CausalSuperluminalTransportPromotion
causalFTLObligationsExist = FTL.canonicalCausalSuperluminalTransportPromotion

causalFTLWitnessRequiresTransport :
  {candidate : FTL.CausalSuperluminalTransportPromotion} →
  (witness : FTL.CausalSuperluminalTransportWitness candidate) →
  FTL.controllableInformationOrMatterTransport candidate ≡ true
causalFTLWitnessRequiresTransport witness =
  FTL.transportReceiptIsTrue witness

causalFTLWitnessRequiresSpacelikeTiming :
  {candidate : FTL.CausalSuperluminalTransportPromotion} →
  (witness : FTL.CausalSuperluminalTransportWitness candidate) →
  FTL.spacelikeSeparationReceipt candidate ≡ true
causalFTLWitnessRequiresSpacelikeTiming witness =
  FTL.spacelikeReceiptIsTrue witness

causalFTLWitnessRequiresReplication :
  {candidate : FTL.CausalSuperluminalTransportPromotion} →
  (witness : FTL.CausalSuperluminalTransportWitness candidate) →
  FTL.independentReplication candidate ≡ true
causalFTLWitnessRequiresReplication witness =
  FTL.replicationReceiptIsTrue witness

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
