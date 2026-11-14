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
import Data.Fin.Base as F
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

------------------------------------------------------------------------
-- ALL 27 original Cartesian 3×3 one-to-one-to-one axis-line seams.
-- These are native cubical paths, each with exactly two positive
-- original bonds. All seams use the existing original pants interface
-- but material conservation is proved from shared 3D voxels.
------------------------------------------------------------------------

xAxisLineSeam :
  (y z : SSP.SSPTrit) → PhysicalPantsBondSeam
xAxisLineSeam y z =
  physical-pants-bond-seam
    (Grid.xBond Grid.lower y z)
    (Grid.xBond Grid.upper y z)
    refl
    Pants.selectedChannel2
    Pants.innerInputChannel2
    Pants.outerInnerMatch

yAxisLineSeam :
  (x z : SSP.SSPTrit) → PhysicalPantsBondSeam
yAxisLineSeam x z =
  physical-pants-bond-seam
    (Grid.yBond x Grid.lower z)
    (Grid.yBond x Grid.upper z)
    refl
    Pants.selectedChannel2
    Pants.innerInputChannel2
    Pants.outerInnerMatch

zAxisLineSeam :
  (x y : SSP.SSPTrit) → PhysicalPantsBondSeam
zAxisLineSeam x y =
  physical-pants-bond-seam
    (Grid.zBond x y Grid.lower)
    (Grid.zBond x y Grid.upper)
    refl
    Pants.selectedChannel2
    Pants.innerInputChannel2
    Pants.outerInnerMatch

allXLineSeams : List PhysicalPantsBondSeam
allXLineSeams =
  Grid.flatMap (λ y → Grid.mapList (xAxisLineSeam y) Grid.trits)
    Grid.trits

allYLineSeams : List PhysicalPantsBondSeam
allYLineSeams =
  Grid.flatMap (λ x → Grid.mapList (yAxisLineSeam x) Grid.trits)
    Grid.trits

allZLineSeams : List PhysicalPantsBondSeam
allZLineSeams =
  Grid.flatMap (λ x → Grid.mapList (zAxisLineSeam x) Grid.trits)
    Grid.trits

all27PhysicalPantsSeams : List PhysicalPantsBondSeam
all27PhysicalPantsSeams =
  Grid.append allXLineSeams
    (Grid.append allYLineSeams allZLineSeams)

allOriginalPantsSeamLinesCount27 :
  Grid.countList all27PhysicalPantsSeams ≡ 27
allOriginalPantsSeamLinesCount27 = refl

-- No independent edge-local material stocks: every two-bond seam
-- is written into the same original 27-voxel vector at each step.
twoOriginalBondActions :
  PhysicalPantsBondSeam →
  List (F.Fin 27 × F.Fin 27)
twoOriginalBondActions seam =
  ( Vector369.originalPointIndex (Grid.bondStart (incomingBond seam))
  , Vector369.originalPointIndex (Grid.bondEnd (incomingBond seam)) )
  ∷ ( Vector369.originalPointIndex (Grid.bondStart (outgoingBond seam))
     , Vector369.originalPointIndex (Grid.bondEnd (outgoingBond seam)) )
  ∷ []

all54PhysicalPantsBondActions :
  List (F.Fin 27 × F.Fin 27)
all54PhysicalPantsBondActions =
  Grid.flatMap twoOriginalBondActions all27PhysicalPantsSeams

everyPantsSeamHasTwoOriginalBondActions :
  (seam : PhysicalPantsBondSeam) →
  Grid.countList (twoOriginalBondActions seam) ≡ 2
everyPantsSeamHasTwoOriginalBondActions seam = refl

originalPantsBondActionsCount54 :
  Grid.countList all54PhysicalPantsBondActions ≡ 54
originalPantsBondActionsCount54 = refl

allPantsGluedPhysicalBondHistoryConserves :
  (state : V.Vec Nat 27) →
  V.sum (Transfer.runTransfers all54PhysicalPantsBondActions state)
    ≡ V.sum state
allPantsGluedPhysicalBondHistoryConserves =
  Transfer.all27SharedSitesConserve all54PhysicalPantsBondActions

-- The seam matching predicate concerns five ORIGINAL informational
-- channel values; it is not a biological flux coefficient.
