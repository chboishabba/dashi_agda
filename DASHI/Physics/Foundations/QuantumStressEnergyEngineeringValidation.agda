{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.QuantumStressEnergyEngineeringValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Foundations.QuantumStressEnergyEngineeringBridgeExact as Bridge

stageRouteExists : Bridge.QuantumStressEngineeringChain
stageRouteExists = Bridge.canonicalQuantumStressEngineeringChain

paymentLedgerExists : Bridge.QuantumStressPaymentLedger
paymentLedgerExists = Bridge.canonicalQuantumStressPaymentLedger

canonicalWarpPaymentRemainsFalse :
  Bridge.warpOrWormholePayment Bridge.canonicalQuantumStressPaymentLedger ≡ false
canonicalWarpPaymentRemainsFalse = Bridge.canonicalWarpOrWormholePaymentIsFalse

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

routeDoesNotPayStages : Bool
routeDoesNotPayStages =
  Bridge.allowedRouteDoesNotCreatePhysicalPayment
    Bridge.canonicalQuantumStressBoundary

metricBackreactionNotWarpPromotion : Bool
metricBackreactionNotWarpPromotion =
  Bridge.metricPerturbationDoesNotPromoteWarpCapability
    Bridge.canonicalQuantumStressBoundary
