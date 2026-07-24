module DASHI.Cognition.PNF.BraidLearningTransport where

open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Cognition.PNF.MemoryFibre as Memory

data PNFLane : Set where
  memoryLane expectationLane desireLane avoidanceLane actionLane observationLane : PNFLane

record PNFLaneState : Set where
  constructor pnfLaneState
  field
    lane : PNFLane
    event : PNF.EventPNF
    laneContext : String

open PNFLaneState public

data BraidTransportOutcome : Set where
  transported : PNFLaneState → String → BraidTransportOutcome
  transportResidual : String → BraidTransportOutcome
  transportUndetermined : String → BraidTransportOutcome
  transportIncompatible : String → BraidTransportOutcome

data BraidComparison : Set where
  coherent equivalentUnderQuotient residuallyDifferent incompatible : BraidComparison

memoryToAvoidance : Memory.MemoryFibre → PNF.EventPNF → BraidTransportOutcome
memoryToAvoidance memory avoided =
  transported
    (pnfLaneState avoidanceLane avoided
      "memory valuation/salience constrains avoided-future lane")
    "beta_M_to_A"

expectationToAction : Memory.ExpectationFibre → PNF.EventPNF → BraidTransportOutcome
expectationToAction expectation action =
  transported
    (pnfLaneState actionLane action
      "expected-future fibre constrains action-policy lane")
    "beta_E_to_U"

record BraidOrderReceipt : Set where
  constructor braidOrderReceipt
  field
    firstOrderLabel secondOrderLabel : String
    comparison : BraidComparison
    residualReceipt : String

open BraidOrderReceipt public

canonicalNonCommutingBraid : BraidOrderReceipt
canonicalNonCommutingBraid =
  braidOrderReceipt
    "memory-to-expectation then expectation-to-action"
    "memory-to-action then expectation-to-memory"
    residuallyDifferent
    "transport order changes the retained provenance and action-bias residual"
