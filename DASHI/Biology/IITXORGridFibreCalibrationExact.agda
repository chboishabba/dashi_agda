module DASHI.Biology.IITXORGridFibreCalibrationExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IITXORGridAdversarialExact as Grid
import DASHI.Biology.IITXORGridFibreCircuitBridgeExact as Circuit
import DASHI.Biology.IIT4FiniteExecutableKernelExact as Kernel

------------------------------------------------------------------------
-- CALIBRATION OWNER: REPO XOR GRID -> VERSIONED IIT SYSTEM-PHI REFERENCE
--
-- The Agda side owns the exact grid dynamics and the recurrence/gluing graph.
-- The numerical phi values are produced by scripts/iit_xor_grid_calibration.py
-- through the versioned finite reference evaluator.  This file records what
-- that execution is allowed to establish without promoting a Python receipt to
-- a kernel theorem.
------------------------------------------------------------------------

repoGridStep : Grid.Grid2x2 → Grid.Grid2x2
repoGridStep = Grid.gridStep

northWestNorthEastRecurrence :
  Circuit.TwoEdgeCircuit Circuit.northWestSite Circuit.northEastSite
northWestNorthEastRecurrence = Circuit.northWestNorthEastCircuit

record XORGridCalibrationReceipt : Set where
  constructor xorGridCalibrationReceipt
  field
    stateCount : Nat
    iit42023ObservedZeroStateCount : Nat
    iit42023ObservedPositiveStateCount : Nat
    iit42023ObservedPositiveValueText : String
    iit42026ObservedZeroStateCount : Nat
    pythonReferenceReceipt : String

open XORGridCalibrationReceipt public

currentXORGridCalibrationReceipt : XORGridCalibrationReceipt
currentXORGridCalibrationReceipt =
  xorGridCalibrationReceipt
    16 12 4 "0.5 bits on the four positive states" 16
    "scripts/iit_xor_grid_calibration.py; exhaustive finite state + directional-partition scan"

record XORGridCalibrationBoundary : Set where
  constructor xorGridCalibrationBoundary
  field
    gridIsRecurrentFabric : Bool
    localRuleIsRepoNativeXor : Bool
    pythonScanUsesVersionedKernelReference : Bool
    iit42023And2026ResultsKeptSeparate : Bool
    graphMidcutCountEqualsSystemPhiByDefinition : Bool
    historicalIITQuantityEqualsIIT4BigPhiByDefinition : Bool
    pythonNumericReceiptIsKernelProof : Bool

open XORGridCalibrationBoundary public

canonicalXORGridCalibrationBoundary : XORGridCalibrationBoundary
canonicalXORGridCalibrationBoundary =
  xorGridCalibrationBoundary true true true true false false false

graphCutStillNotPhi :
  graphMidcutCountEqualsSystemPhiByDefinition
    canonicalXORGridCalibrationBoundary ≡ false
graphCutStillNotPhi = refl

pythonCalibrationDoesNotPromoteToKernel :
  pythonNumericReceiptIsKernelProof
    canonicalXORGridCalibrationBoundary ≡ false
pythonCalibrationDoesNotPromoteToKernel = refl

versionedKernelBoundary : Kernel.IIT4ExecutableKernelBoundary
versionedKernelBoundary = Kernel.canonicalIIT4ExecutableKernelBoundary
