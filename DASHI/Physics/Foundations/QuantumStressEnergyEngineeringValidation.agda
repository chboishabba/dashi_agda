{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.QuantumStressEnergyEngineeringValidation where

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.Foundations.QuantumStressEnergyEngineeringBridgeExact as Bridge

stageChainExists : Bridge.QuantumStressEngineeringChain
stageChainExists = Bridge.canonicalQuantumStressEngineeringChain

casimirBackreactionObligationExists : Bridge.CasimirBackreactionObligation
casimirBackreactionObligationExists = Bridge.canonicalCasimirBackreactionObligation

energyConditionViolationNotAutomaticImpossibility : Bool
energyConditionViolationNotAutomaticImpossibility =
  Bridge.energyConditionViolationDoesNotMeanUnphysical
    Bridge.canonicalQuantumStressBoundary

energyConditionViolationNotEngineeringReceipt : Bool
energyConditionViolationNotEngineeringReceipt =
  Bridge.energyConditionViolationDoesNotMeanEngineeringRealizable
    Bridge.canonicalQuantumStressBoundary

metricBackreactionNotWarpPromotion : Bool
metricBackreactionNotWarpPromotion =
  Bridge.metricPerturbationDoesNotPromoteWarpCapability
    Bridge.canonicalQuantumStressBoundary
