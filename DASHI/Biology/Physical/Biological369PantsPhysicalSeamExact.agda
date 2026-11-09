module DASHI.Biology.Physical.Biological369PantsPhysicalSeamExact where

------------------------------------------------------------------------
-- ORIGINAL 3x3x3 BIOLOGICAL GEOMETRY / PANTS-SEAM WELD.
--
-- The actual physical carrier is Cube.Ternary27Point = SSPTrit^3;
-- Vec Nat 27 is merely its lossless enumerated material-value chart.
-- A seam glues two physically incident (native) bonds ONLY when their
-- shared voxel matches and the selected pants-interface boundary
-- values satisfy ALL five original interface comparisons.
--
-- This is a finite combinatorial material-bond / branch-interface
-- correspondence, NOT a smooth pants surface, TQFT, automatically
-- reconstructed vasculature, or measured physiological permeability.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Data.Vec.Base as V
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Biology.Physical.BiologicalFullCubeIncidenceExact as Grid
import DASHI.Biology.Physical.BiologicalOriginal54BondSharedVectorExact as Vector369
import DASHI.Biology.Physical.BiologicalSharedFiniteVectorTransferExact as Transfer
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Reasoning.TypedHyperfabricPantsGluingBridgeExact as TypedPants
import DASHI.Topology.TernaryCylinderPantsGeometryExact as CylinderPants

record PhysicalPantsBondSeam : Set where
  constructor physical-pants-bond-seam
  field
    incomingBond : Grid.PositiveBond
    outgoingBond : Grid.PositiveBond
    samePhysicalVoxel :
      Grid.bondEnd incomingBond ≡ Grid.bondStart outgoingBond
    inputChannel : Pants.BranchChannel
    outputChannel : Pants.BranchChannel
    originalFiveCoordinateMatch :
      Pants.InterfaceMatch inputChannel outputChannel

open PhysicalPantsBondSeam public

-- One selected 369 x-axis fibre has two native consecutive bonds:
-- (-1,0,0)->(0,0,0)->(+1,0,0). The pants seam is the *same original*
-- outer-selected-leg to inner-waist match already proved in DASHI.
canonicalIncomingBond : Grid.PositiveBond
canonicalIncomingBond =
  Grid.xBond Grid.lower SSP.sspZero SSP.sspZero

canonicalOutgoingBond : Grid.PositiveBond
canonicalOutgoingBond =
  Grid.xBond Grid.upper SSP.sspZero SSP.sspZero

canonical369PhysicalPantsSeam : PhysicalPantsBondSeam
canonical369PhysicalPantsSeam =
  physical-pants-bond-seam
    canonicalIncomingBond
    canonicalOutgoingBond
    refl
    Pants.selectedChannel2
    Pants.innerInputChannel2
    Pants.outerInnerMatch

canonicalSeamKeepsOriginalCommonVoxel :
  Grid.bondEnd (incomingBond canonical369PhysicalPantsSeam)
    ≡ Grid.bondStart (outgoingBond canonical369PhysicalPantsSeam)
canonicalSeamKeepsOriginalCommonVoxel =
  samePhysicalVoxel canonical369PhysicalPantsSeam

canonicalSeamIsCanonicalFiveCoordinatePantsMatch :
  originalFiveCoordinateMatch canonical369PhysicalPantsSeam
    ≡ Pants.outerInnerMatch
canonicalSeamIsCanonicalFiveCoordinatePantsMatch = refl

seamPropositionAgrees :
  (seam : PhysicalPantsBondSeam) →
  Pants.propositionType (Pants.channelBoundary (inputChannel seam))
    ≡ Pants.propositionType (Pants.channelBoundary (outputChannel seam))
seamPropositionAgrees seam =
  Pants.propositionMatches (originalFiveCoordinateMatch seam)

seamCapacityAgrees :
  (seam : PhysicalPantsBondSeam) →
  Pants.boundaryCapacity (Pants.channelBoundary (inputChannel seam))
    ≡ Pants.boundaryCapacity (Pants.channelBoundary (outputChannel seam))
seamCapacityAgrees seam =
  Pants.capacityMatches (originalFiveCoordinateMatch seam)

seamPhaseAgrees :
  (seam : PhysicalPantsBondSeam) →
  Pants.boundaryPhase (Pants.channelBoundary (inputChannel seam))
    ≡ Pants.boundaryPhase (Pants.channelBoundary (outputChannel seam))
seamPhaseAgrees seam =
  Pants.phaseMatches (originalFiveCoordinateMatch seam)

seamWaveAgrees :
  (seam : PhysicalPantsBondSeam) →
  Pants.channelWave (inputChannel seam)
    ≡ Pants.channelWave (outputChannel seam)
seamWaveAgrees seam =
  Pants.waveMatches (originalFiveCoordinateMatch seam)

seamOpennessAgrees :
  (seam : PhysicalPantsBondSeam) →
  Pants.boundaryOpen (Pants.channelBoundary (inputChannel seam))
    ≡ Pants.boundaryOpen (Pants.channelBoundary (outputChannel seam))
seamOpennessAgrees seam =
  Pants.opennessMatches (originalFiveCoordinateMatch seam)

seamIncomingTransport :
  PhysicalPantsBondSeam →
  V.Vec Nat 27 → V.Vec Nat 27
seamIncomingTransport seam state =
  Transfer.transferOne
    (Vector369.originalPointIndex (Grid.bondStart (incomingBond seam)))
    (Vector369.originalPointIndex (Grid.bondEnd (incomingBond seam)))
    state

seamOutgoingTransport :
  PhysicalPantsBondSeam →
  V.Vec Nat 27 → V.Vec Nat 27
seamOutgoingTransport seam state =
  Transfer.transferOne
    (Vector369.originalPointIndex (Grid.bondStart (outgoingBond seam)))
    (Vector369.originalPointIndex (Grid.bondEnd (outgoingBond seam)))
    state

-- Transport preserves one and the SAME original shared 27-site
-- material state, across the original two geometrically incident
-- pants-certified physical bonds. The seam itself never creates mass.
gluedSeamTransportPreservesOriginalTotal :
  (seam : PhysicalPantsBondSeam)
  (state : V.Vec Nat 27) →
  V.sum (seamOutgoingTransport seam (seamIncomingTransport seam state))
    ≡ V.sum state
gluedSeamTransportPreservesOriginalTotal seam state =
  trans
    (Transfer.everyDirectedPairConservesSharedInventory
      (Vector369.originalPointIndex (Grid.bondStart (outgoingBond seam)))
      (Vector369.originalPointIndex (Grid.bondEnd (outgoingBond seam)))
      (seamIncomingTransport seam state))
    (Transfer.everyDirectedPairConservesSharedInventory
      (Vector369.originalPointIndex (Grid.bondStart (incomingBond seam)))
      (Vector369.originalPointIndex (Grid.bondEnd (incomingBond seam)))
      state)

-- Existing unrelated theorem owners MUST be imported, not duplicated:
existingThreePantsOutputs : Pants.outputCount Pants.composedOneToThree ≡ 3
existingThreePantsOutputs = CylinderPants.canonicalPantsHasThreeOutputs

existingPantsCapacityConservation :
  Pants.CapacityConservative Pants.composedOneToThree
existingPantsCapacityConservation =
  CylinderPants.canonicalPantsCapacityConservative

existingHyperfabricSeam :
  TypedPants.HyperfabricPantsGluing TypedPants.seamSection
existingHyperfabricSeam = TypedPants.canonicalPantsGluing

-- A matching informational/cobordism branch interface NEVER grants
-- a measured physical flux, membrane permeability, or material
-- source automatically. Those are source- and context-specific.
data PantsMatchAutomaticallyPaysPhysicalFlow : Set where

noAutomaticPhysicalFlowFromPants :
  PantsMatchAutomaticallyPaysPhysicalFlow → ⊥
noAutomaticPhysicalFlowFromPants ()
