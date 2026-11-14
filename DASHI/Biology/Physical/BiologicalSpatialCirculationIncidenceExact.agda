module DASHI.Biology.Physical.BiologicalSpatialCirculationIncidenceExact where

------------------------------------------------------------------------
-- Explicit directed circulation/conductance over the ORIGINAL 54-bond
-- nonperiodic 3x3x3 topology; do not replace compartments with a global
-- chemical scalar. Transport law imported from original finite
-- electrodiffusive/moving boundary donor (not a fabricated calibration).
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Biology.Physical.BiologicalFullCubeIncidenceExact as Grid
import DASHI.Biology.Physical.BiologicalAllNeighbourTissueDynamicsExact as Tissue
import DASHI.Biology.Physical.FiniteElectrodiffusiveMovingBoundaryExact as Transport
import DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact as PNP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube

record DirectedTissueCirculation : Set₁ where
  field
    originalPhysicalSource : String
    sourceCompartment : String
    targetCompartment : String
    sourceTime : String
    selectedElectrodiffusion : PNP.ElectrodiffusionApplicationReceipt
    -- A physical bond cannot be invented between nonadjacent voxels:
    -- the edge carrier proves native nearest-neighbour incidence.
    allowForward : Grid.PositiveBond → Bool
    allowReverse : Grid.PositiveBond → Bool
    forwardFlowReference : Grid.PositiveBond → String
    reverseFlowReference : Grid.PositiveBond → String
    -- Per-bond measurements must come from the selected original
    -- tissue/source; no global pool amount gives these values.
    originalBondState : Grid.PositiveBond → Transport.IonPairState

open DirectedTissueCirculation public

transportOnDirectedBond :
  DirectedTissueCirculation →
  Grid.PositiveBond → Transport.IonPairState
transportOnDirectedBond network edge
  with allowForward network edge | allowReverse network edge
... | true | _ =
  Transport.transport Transport.leftToRight (originalBondState network edge)
... | false | true =
  Transport.transport Transport.rightToLeft (originalBondState network edge)
... | false | false = originalBondState network edge

directedBondConservesAmount :
  (network : DirectedTissueCirculation)
  (edge : Grid.PositiveBond) →
  Transport.totalAmount (transportOnDirectedBond network edge)
    ≡ Transport.totalAmount (originalBondState network edge)
directedBondConservesAmount network edge
  with allowForward network edge | allowReverse network edge
... | true | _ =
  Transport.transportConservesAmount
    Transport.leftToRight (originalBondState network edge)
... | false | true =
  Transport.transportConservesAmount
    Transport.rightToLeft (originalBondState network edge)
... | false | false = refl

directedBondConservesCharge :
  (valenceMagnitude : Nat)
  (network : DirectedTissueCirculation)
  (edge : Grid.PositiveBond) →
  Transport.chargeMagnitude valenceMagnitude
    (transportOnDirectedBond network edge)
    ≡
  Transport.chargeMagnitude valenceMagnitude
    (originalBondState network edge)
directedBondConservesCharge z network edge =
  cong (λ amount → z * amount)
    (directedBondConservesAmount network edge)

-- The *same* geometric and ionic 54-bond skeleton can support
-- different circulatory permissions. The selected branch direction
-- is therefore an independent source variable.
record VoxelPhysicalTransportRefinement : Set₁ where
  field
    spatialCirculation : DirectedTissueCirculation
    physicalState : Set
    physicalAdvance : physicalState → physicalState
    physicalAt : physicalState → Cube.Ternary27Point → Nat
    -- To derive an actual conservation theorem on shared 27-voxel
    -- state rather than duplicated per-edge states, require this
    -- finite-volume continuity equation from the selected update.
    fluxDivergence : physicalState → Cube.Ternary27Point → Nat
    sourceInjection : physicalState → Cube.Ternary27Point → Nat
    netBalanceReference : String
    -- Rates and signed divergences require the separately selected
    -- physical law: all terms here are unsigned, deliberately not
    -- asserted to satisfy a fake conservation equation.
