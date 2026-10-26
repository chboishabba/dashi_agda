module DASHI.Biology.IITMatchedFabricGateExperimentExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IITCausalPantsFibreGluingExact as Pants
import DASHI.Biology.IITXORGridFibreCircuitBridgeExact as Grid
import DASHI.Biology.IIT4FiniteExecutableKernelExact as Kernel

------------------------------------------------------------------------
-- MATCHED EXPERIMENT AXES
--
-- System integration is evaluated on an assembled causal object.  The two
-- experiment coordinates below are intentionally independent:
--
--   H  = gluing/fabric topology
--   mu = local synthesis algebra
--
-- The current state is a third coordinate.  Neither H nor mu alone is a
-- definition of IIT system phi.
------------------------------------------------------------------------

data FabricKind : Set where
  feedForwardFabric : FabricKind
  recurrentThreeCellFabric : FabricKind
  xorGrid2x2Fabric : FabricKind
  ternaryPantsPathFabric : FabricKind

data GateKind : Set where
  booleanXorGate : GateKind
  booleanOrGate : GateKind
  booleanAndGate : GateKind
  ternaryTriXorGate : GateKind

record MatchedExperimentPoint : Set where
  constructor matchedExperimentPoint
  field
    fabric : FabricKind
    gate : GateKind
    stateLabel : String

open MatchedExperimentPoint public

sameFabricXor : MatchedExperimentPoint
sameFabricXor =
  matchedExperimentPoint recurrentThreeCellFabric booleanXorGate "state varies"

sameFabricOr : MatchedExperimentPoint
sameFabricOr =
  matchedExperimentPoint recurrentThreeCellFabric booleanOrGate "state varies"

sameFabricAnd : MatchedExperimentPoint
sameFabricAnd =
  matchedExperimentPoint recurrentThreeCellFabric booleanAndGate "state varies"

sameFabricTriXor : MatchedExperimentPoint
sameFabricTriXor =
  matchedExperimentPoint recurrentThreeCellFabric ternaryTriXorGate "state varies"

sameGateFeedForward : MatchedExperimentPoint
sameGateFeedForward =
  matchedExperimentPoint feedForwardFabric booleanXorGate "state varies"

sameGateRecurrent : MatchedExperimentPoint
sameGateRecurrent = sameFabricXor

sameGateGrid : MatchedExperimentPoint
sameGateGrid =
  matchedExperimentPoint xorGrid2x2Fabric booleanXorGate "state varies"

------------------------------------------------------------------------
-- Existing exact witnesses that the coordinates are not collapsed.
------------------------------------------------------------------------

sameWiringDifferentBooleanGateChangesOutput :
  Pants.evaluateGluedCell Pants.sameBoolWiring Pants.boolXorCell true true
  ≡ Pants.evaluateGluedCell Pants.sameBoolWiring Pants.boolOrCell true true
  → ⊥
sameWiringDifferentBooleanGateChangesOutput =
  Pants.sameFabricDifferentLocalAlgebraChangesOutput

gridRecurrenceExistsIndependentlyOfXorValue :
  Grid.TwoEdgeCircuit Grid.northWestSite Grid.northEastSite
gridRecurrenceExistsIndependentlyOfXorValue = Grid.northWestNorthEastCircuit

------------------------------------------------------------------------
-- Numerical receipt boundary.
------------------------------------------------------------------------

record MatchedSweepReceipt : Set where
  constructor matchedSweepReceipt
  field
    fixedRecurrentXor2023 : String
    fixedRecurrentOr2023 : String
    fixedRecurrentAnd2023 : String
    fixedRecurrentTriXor2023 : String
    fixedXorFeedForward2023 : String
    fixedXorGrid2023 : String
    deterministic2026Receipt : String
    scanner : String

open MatchedSweepReceipt public

currentMatchedSweepReceipt : MatchedSweepReceipt
currentMatchedSweepReceipt = matchedSweepReceipt
  "XOR: phi_s=2 on all 8 states"
  "OR: phi_s in {0, log2(4/3), 2}; six of eight states zero"
  "AND: same value profile as OR; six of eight states zero"
  "triXor: phi_s=log2(9) on all 27 states"
  "feed-forward XOR: phi_s=0"
  "2x2 recurrent XOR grid: phi_s in {0,0.5}; twelve of sixteen states zero"
  "under IIT_4_0_2026 every deterministic fixture in this sweep has phi_s=0"
  "scripts/iit_matched_fabric_gate_sweep.py"

record MatchedExperimentBoundary : Set where
  constructor matchedExperimentBoundary
  field
    fabricAndGateAreSeparateCoordinates : Bool
    sameFabricMayCarryDifferentGates : Bool
    sameGateMayLiveOnDifferentFabrics : Bool
    currentStateIsIndependentCoordinate : Bool
    fabricAloneDeterminesPhiByDefinition : Bool
    gateAloneDeterminesPhiByDefinition : Bool
    pythonSweepIsKernelProof : Bool

open MatchedExperimentBoundary public

canonicalMatchedExperimentBoundary : MatchedExperimentBoundary
canonicalMatchedExperimentBoundary =
  matchedExperimentBoundary true true true true false false false

fabricDoesNotDefinitionallyDeterminePhi :
  fabricAloneDeterminesPhiByDefinition canonicalMatchedExperimentBoundary ≡ false
fabricDoesNotDefinitionallyDeterminePhi = refl

gateDoesNotDefinitionallyDeterminePhi :
  gateAloneDeterminesPhiByDefinition canonicalMatchedExperimentBoundary ≡ false
gateDoesNotDefinitionallyDeterminePhi = refl

versionBoundary : Kernel.IIT4ExecutableKernelBoundary
versionBoundary = Kernel.canonicalIIT4ExecutableKernelBoundary
