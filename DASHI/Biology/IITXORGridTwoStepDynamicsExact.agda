module DASHI.Biology.IITXORGridTwoStepDynamicsExact where

open import DASHI.Core.Prelude
import DASHI.Biology.IITXORGridAdversarialExact as Grid
import DASHI.Biology.IITXORGridFibreCircuitBridgeExact as Circuit
import DASHI.Biology.StateDependentMultiplexTransducer as XOR

------------------------------------------------------------------------
-- DASHI-derived exact dynamics of the EXISTING repo-native 2x2 XOR grid.
-- This is NOT a new XOR semantics and is NOT an IIT Phi calculation.
--
-- x = (NW, NE, SW, SE)
-- F(x) = (NE xor SW, NW xor SE, NW xor SE, NE xor SW).
--
-- Its directed causal fabric has two-edge feedback circuits, but the exact
-- Boolean transition map is nilpotent of index 2: F(F(x)) = zero.
-- Therefore structural recurrence does not guarantee persistent nonzero
-- activity or retention of the four-bit state. This does not invalidate
-- state-specific IIT analyses, nor identify any conscious/phenomenal state.
--
-- Primary provenance: the authors of the historical XOR-grid/IIT debate
-- (Scott Aaronson 2014 critique and Giulio Tononi 2014 response) own their
-- positions. DASHI owns this finite 2x2 model-derived witness, not a
-- reanalysis of the historical infinite/large-grid construction.
------------------------------------------------------------------------

zeroGrid : Grid.Grid2x2
zeroGrid = Grid.grid2x2 false false false false

twoStepNilpotence :
  (state : Grid.Grid2x2) →
  Grid.gridStep (Grid.gridStep state) ≡ zeroGrid
twoStepNilpotence (Grid.grid2x2 false false false false) = refl
twoStepNilpotence (Grid.grid2x2 false false false true) = refl
twoStepNilpotence (Grid.grid2x2 false false true false) = refl
twoStepNilpotence (Grid.grid2x2 false false true true) = refl
twoStepNilpotence (Grid.grid2x2 false true false false) = refl
twoStepNilpotence (Grid.grid2x2 false true false true) = refl
twoStepNilpotence (Grid.grid2x2 false true true false) = refl
twoStepNilpotence (Grid.grid2x2 false true true true) = refl
twoStepNilpotence (Grid.grid2x2 true false false false) = refl
twoStepNilpotence (Grid.grid2x2 true false false true) = refl
twoStepNilpotence (Grid.grid2x2 true false true false) = refl
twoStepNilpotence (Grid.grid2x2 true false true true) = refl
twoStepNilpotence (Grid.grid2x2 true true false false) = refl
twoStepNilpotence (Grid.grid2x2 true true false true) = refl
twoStepNilpotence (Grid.grid2x2 true true true false) = refl
twoStepNilpotence (Grid.grid2x2 true true true true) = refl

-- The exact image is indexed by only two Boolean parity coordinates,
-- despite four input sites. No cardinality statement is smuggled into
-- this image-form theorem.
imageForm : Bool → Bool → Grid.Grid2x2
imageForm p q = Grid.grid2x2 p q q p

stepFactorsThroughTwoParities :
  (state : Grid.Grid2x2) →
  Grid.gridStep state
  ≡ imageForm
      (XOR.xor (Grid.northEast state) (Grid.southWest state))
      (XOR.xor (Grid.northWest state) (Grid.southEast state))
stepFactorsThroughTwoParities state = refl

-- Each of the four (p,q) parity outputs is actually realised.  This
-- does not assert a unique preimage; the Python enumeration checks sizes.
allParityOutputsRealised :
  (p q : Bool) →
  Grid.gridStep (Grid.grid2x2 q p false false)
  ≡ imageForm p q
allParityOutputsRealised false false = refl
allParityOutputsRealised false true = refl
allParityOutputsRealised true false = refl
allParityOutputsRealised true true = refl

directedCycleStillPresent :
  Circuit.TwoEdgeCircuit Circuit.northWestSite Circuit.northEastSite
directedCycleStillPresent = Circuit.northWestNorthEastCircuit

canonicalStepNonzero : Grid.gridStep Grid.canonicalGridInput ≡ zeroGrid → ⊥
canonicalStepNonzero ()

record RecurrentNilpotentInterpretationBoundary : Set where
  constructor recurrent-nilpotent-interpretation-boundary
  field
    sourceGridDynamicsReused : Bool
    twoStepNilpotenceWitness : Bool
    explicitRecurrenceWitness : Bool
    twoParityOutputFactorization : Bool
    graphRecurrenceImpliesNonzeroPersistentActivity : Bool
    graphCyclesDefinitionallyDetermineIITPhi : Bool
    outputGeometryEstablishesPhenomenalConsciousness : Bool

canonicalRecurrentNilpotentBoundary : RecurrentNilpotentInterpretationBoundary
canonicalRecurrentNilpotentBoundary =
  recurrent-nilpotent-interpretation-boundary
    true true true true false false false
