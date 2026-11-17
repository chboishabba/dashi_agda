module DASHI.Biology.IITXORGridSynthesisFabricExact where

------------------------------------------------------------------------
-- XOR GRID = A FABRIC OF ORDERED TWO-INPUT / ONE-OUTPUT SYNTHESIS CELLS
--
-- This is the grid-wide version of IITXORGridFibreCircuitBridgeExact.
-- Every site owns the same trivalent causal shape
--
--      sourceA ----\
--                   XOR ----> target output
--      sourceB ----/
--
-- and the global network is obtained by routing earlier/current site outputs
-- into the named A/B sockets of every target site.  Thus the historical large
-- XOR grid and the repo's dialectic/trialectic synthesis cells have the same
-- local causal arity.  What differs is the local algebra and the gluing fabric.
--
-- XOR is symmetric: swapping A/B leaves the local output unchanged.  The
-- wiring nevertheless retains distinct named A/B ports.  This is exactly the
-- distinction needed for the torque/369 comparison: an orientation-capable
-- fabric can host an orientation-blind XOR law, while an antisymmetric ternary
-- law may consume the same ordering as handedness data.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.StateDependentMultiplexTransducer as XOR
import DASHI.Biology.IITCausalPantsFibreGluingExact as Pants
import DASHI.Biology.IITXORGridAdversarialExact as Grid
import DASHI.Biology.IITXORGridFibreCircuitBridgeExact as Circuit

------------------------------------------------------------------------
-- 1. Generic two-source fabric on an arbitrary site carrier.
------------------------------------------------------------------------

record TwoInputFabric (Site : Set) : Set where
  constructor two-input-fabric
  field
    inputASource : Site → Site
    inputBSource : Site → Site
open TwoInputFabric public

BoolField : Set → Set
BoolField Site = Site → Bool

xorFabricStep :
  {Site : Set} →
  TwoInputFabric Site →
  BoolField Site →
  BoolField Site
xorFabricStep fabric state target =
  XOR.xor
    (state (inputASource fabric target))
    (state (inputBSource fabric target))

------------------------------------------------------------------------
-- 2. Every target site literally inhabits the generic causal-pants ABI.
------------------------------------------------------------------------

siteBoolFamily : {Site : Set} → Pants.FibreFamily Site
siteBoolFamily = record { Fibre = λ _ → Bool }

wireAAt :
  {Site : Set} →
  (fabric : TwoInputFabric Site) →
  (target : Site) →
  Pants.OutputInputGluing
    siteBoolFamily
    (inputASource fabric target)
    target
wireAAt fabric target = record
  { targetPort = Pants.inputA
  ; transport = λ x → x
  }

wireBAt :
  {Site : Set} →
  (fabric : TwoInputFabric Site) →
  (target : Site) →
  Pants.OutputInputGluing
    siteBoolFamily
    (inputBSource fabric target)
    target
wireBAt fabric target = record
  { targetPort = Pants.inputB
  ; transport = λ x → x
  }

wiringAt :
  {Site : Set} →
  (fabric : TwoInputFabric Site) →
  (target : Site) →
  Pants.TwoSourceInputGluing
    siteBoolFamily
    (inputASource fabric target)
    (inputBSource fabric target)
    target
wiringAt fabric target = record
  { leftWire = wireAAt fabric target
  ; rightWire = wireBAt fabric target
  ; leftTargetsA = refl
  ; rightTargetsB = refl
  }

xorCellAt :
  {Site : Set} →
  (target : Site) →
  Pants.LocalSynthesisCell siteBoolFamily target
xorCellAt target = record { combine = XOR.xor }

gluedXorEqualsFabricStep :
  {Site : Set} →
  (fabric : TwoInputFabric Site) →
  (state : BoolField Site) →
  (target : Site) →
  Pants.evaluateGluedCell
    (wiringAt fabric target)
    (xorCellAt target)
    (state (inputASource fabric target))
    (state (inputBSource fabric target))
  ≡ xorFabricStep fabric state target
gluedXorEqualsFabricStep fabric state target = refl

------------------------------------------------------------------------
-- 3. XOR forgets input handedness; the fabric does not.
------------------------------------------------------------------------

xorCommutative : (a b : Bool) → XOR.xor a b ≡ XOR.xor b a
xorCommutative false false = refl
xorCommutative false true = refl
xorCommutative true false = refl
xorCommutative true true = refl

swapFabricInputs : {Site : Set} → TwoInputFabric Site → TwoInputFabric Site
swapFabricInputs fabric =
  two-input-fabric
    (inputBSource fabric)
    (inputASource fabric)

xorStepIgnoresLocalInputOrder :
  {Site : Set} →
  (fabric : TwoInputFabric Site) →
  (state : BoolField Site) →
  (target : Site) →
  xorFabricStep (swapFabricInputs fabric) state target
  ≡ xorFabricStep fabric state target
xorStepIgnoresLocalInputOrder fabric state target =
  xorCommutative
    (state (inputBSource fabric target))
    (state (inputASource fabric target))

inputANotInputB : Pants.inputA ≡ Pants.inputB → ⊥
inputANotInputB ()

namedPortsRemainDistinct :
  {Site : Set} →
  (fabric : TwoInputFabric Site) →
  (target : Site) →
  Pants.targetPort (Pants.leftWire (wiringAt fabric target))
  ≡ Pants.targetPort (Pants.rightWire (wiringAt fabric target)) →
  ⊥
namedPortsRemainDistinct fabric target equality = inputANotInputB equality

------------------------------------------------------------------------
-- 4. Recover the existing 2x2 adversarial fixture pointwise from the generic
--    synthesis fabric.  The special fixture is therefore an instance, not a
--    competing grid semantics.
------------------------------------------------------------------------

grid2x2Fabric : TwoInputFabric Circuit.GridSite
grid2x2Fabric = two-input-fabric sourceA sourceB
  where
    sourceA : Circuit.GridSite → Circuit.GridSite
    sourceA Circuit.northWestSite = Circuit.northEastSite
    sourceA Circuit.northEastSite = Circuit.northWestSite
    sourceA Circuit.southWestSite = Circuit.northWestSite
    sourceA Circuit.southEastSite = Circuit.northEastSite

    sourceB : Circuit.GridSite → Circuit.GridSite
    sourceB Circuit.northWestSite = Circuit.southWestSite
    sourceB Circuit.northEastSite = Circuit.southEastSite
    sourceB Circuit.southWestSite = Circuit.southEastSite
    sourceB Circuit.southEastSite = Circuit.southWestSite

gridState : Grid.Grid2x2 → BoolField Circuit.GridSite
gridState grid Circuit.northWestSite = Grid.northWest grid
gridState grid Circuit.northEastSite = Grid.northEast grid
gridState grid Circuit.southWestSite = Grid.southWest grid
gridState grid Circuit.southEastSite = Grid.southEast grid

grid2x2StepIsCellwiseXorFabric :
  (grid : Grid.Grid2x2) →
  (site : Circuit.GridSite) →
  gridState (Grid.gridStep grid) site
  ≡ xorFabricStep grid2x2Fabric (gridState grid) site
grid2x2StepIsCellwiseXorFabric grid Circuit.northWestSite = refl
grid2x2StepIsCellwiseXorFabric grid Circuit.northEastSite = refl
grid2x2StepIsCellwiseXorFabric grid Circuit.southWestSite = refl
grid2x2StepIsCellwiseXorFabric grid Circuit.southEastSite = refl

------------------------------------------------------------------------
-- 5. Cross-pollination boundary.
--
-- The generic causal-pants owner already proves that the same abstract wiring
-- ABI can host triXor.  Hence Boolean XOR versus ternary/trialectic synthesis
-- is not a change in local causal arity.  It is a change of fibre alphabet and
-- synthesis algebra on an independently specified gluing fabric.
------------------------------------------------------------------------

sameAbstractCellABIAlsoHostsTriXor :
  Pants.sameAbstractWiringCanHostTriXor
    Pants.canonicalIITCausalPantsFibreBoundary ≡ true
sameAbstractCellABIAlsoHostsTriXor = refl

record XORGridSynthesisFabricBoundary : Set where
  constructor xor-grid-synthesis-fabric-boundary
  field
    everyGridSiteIsTwoInputOneOutputCell : Bool
    globalGridIsGluingOfThoseCells : Bool
    inputSocketsRemainNamedAndOrdered : Bool
    xorLocalLawForgetsInputOrdering : Bool
    orderedFabricCanCarryMoreStructureThanXorConsumes : Bool
    sameCellABIHostsTernarySynthesis : Bool
    recurrenceBelongsToInterCellGluing : Bool
    higherOrderSystemOrganizationRequiresHigherArityLocalGate : Bool
    xorSymmetryAloneCreatesTorqueHandedness : Bool

open XORGridSynthesisFabricBoundary public

canonicalXORGridSynthesisFabricBoundary : XORGridSynthesisFabricBoundary
canonicalXORGridSynthesisFabricBoundary =
  xor-grid-synthesis-fabric-boundary
    true
    true
    true
    true
    true
    true
    true
    false
    false

binaryGridDoesNotNeedHigherArityLocalGate :
  higherOrderSystemOrganizationRequiresHigherArityLocalGate
    canonicalXORGridSynthesisFabricBoundary ≡ false
binaryGridDoesNotNeedHigherArityLocalGate = refl

xorDoesNotManufactureTorqueOrientation :
  xorSymmetryAloneCreatesTorqueHandedness
    canonicalXORGridSynthesisFabricBoundary ≡ false
xorDoesNotManufactureTorqueOrientation = refl
