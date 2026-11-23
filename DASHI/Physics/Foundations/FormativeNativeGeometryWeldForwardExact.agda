module DASHI.Physics.Foundations.FormativeNativeGeometryWeldForwardExact where

-- 21 November 2026 | weld FORWARD from original DASHI geometry/theorems.
--
-- Reuses the actual nonperiodic balanced-ternary 3x3x3 coordinate carrier,
-- the 54 native positive bonds and 36 squares, all-neighbour OLD-FIELD
-- morphogenetic updates, the 54-bond future-safe quotient, and the SAME
-- physical-PNP/tissue history consumer.
--
-- A separate selected mesh-face adapter is an identity/coordinate gate into
-- the existing Smith/Filsinger Cayley event. No new electromagnetic
-- constitutive law, gravity coupling, source work or measured BH4 flux is
-- defined or inferred. This is a conditional exact geometric weld, not
-- evidence for the Sheldrake nonlocal hypothesis.
--
-- Provenance: original Base369/369 pants and geometric organization belong
-- to their existing repo owners; original scientific field, tissue,
-- electrodiffusion and Filsinger sources remain in their native modules.
-- Newly composed equations below are DASHI constructions, not claims by
-- Rupert Sheldrake, Michael Levin, Filsinger or the BH4 source authors.

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Biology.Physical.BiologicalFullCubeIncidenceExact as Grid
import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Bio
import DASHI.Biology.Physical.BiologicalCoupledTissueCubeExact as Agreement
import DASHI.Biology.Physical.BiologicalAllNeighbourTissueDynamicsExact as Tissue
import DASHI.Biology.Physical.BiologicalSourcePhysicalTissueSimulationExact as Physical
import DASHI.Physics.Motors.SmithFilsingerIndexedFaceIncidenceExact as Face
import DASHI.Physics.Motors.SmithFilsingerIndexedCayleyFaceWeldExact as Cayley
import DASHI.Physics.Motors.SmithFilsingerLocalCausalADEFrameExact as Frame
import DASHI.Biology.Physical.FiniteElectrodiffusiveMovingBoundaryExact as Diffusion

------------------------------------------------------------------------
-- Q1 native geometric source: no nominal Vec-27 replacement and no periodic
-- wraparound. Grid.PositiveBond is ONE oriented copy of each native edge.
------------------------------------------------------------------------

originalTernarySites : Cube.hypervoxelStateCount ≡ 27
originalTernarySites = Cube.hypervoxelStateCountIs27

originalPositiveBonds : Grid.countList Grid.allPositiveBonds ≡ 54
originalPositiveBonds = Grid.completeBondCount

originalElementarySquares :
  Grid.countList Grid.allElementarySquares ≡ 36
originalElementarySquares = Grid.completePlaquetteCount

originalSixOuterFaces : Cube.outerFaceCount ≡ 6
originalSixOuterFaces = refl

nativeBondReallyAdjacent :
  (edge : Grid.PositiveBond) →
  Cube.HypervoxelAdjacent (Grid.bondStart edge) (Grid.bondEnd edge)
nativeBondReallyAdjacent = Grid.bondIsNearestNeighbour

nativePlaquetteClosesAtOriginalCorner :
  (square : Grid.ElementarySquare) →
  Grid.bondEnd (Grid.upperSecond square)
    ≡ Grid.bondEnd (Grid.upperFirst square)
nativePlaquetteClosesAtOriginalCorner = Grid.squareFinalCorner

-- The morphology operator consumes ALL 54 native bonds, not one hand-picked
-- neighbour and not a periodic C3^3 Fourier group law.
everyNativeBondFeedsSelectedResponse :
  (field : Bio.TissueField) (p : Cube.Ternary27Point) →
  Tissue.allNeighbourFine field p
    ≡ Tissue.fineListIncoming field p Grid.allPositiveBonds
everyNativeBondFeedsSelectedResponse field p = refl

------------------------------------------------------------------------
-- Q4/Q5: forward-weld the existing ONE physical source's PNP history and
-- all-neighbour tissue projection. It is the already specified physical
-- one-step simulation that must be PAID; no constructor is manufactured.
------------------------------------------------------------------------

samePhysicalPNPAndTissueHistory :
  (model : Physical.SourcePhysicalTissueSimulation)
  (actions : List Bio.Intervention)
  (state : Physical.PhysicalState model) →
  (Physical.pnState model (Physical.physicalTrace model actions state)
    ≡ Physical.pnTrace model actions (Physical.pnState model state))
  ×
  Agreement.FieldsAgree
    (Physical.tissueReadout model
      (Physical.physicalTrace model actions state))
    (Tissue.fullCoarseRun actions
      (Bio.spatialProject (Physical.tissueReadout model state)))
samePhysicalPNPAndTissueHistory =
  Physical.physicalPNPAndTissueSameHistory

-- This is the new, nontrivial COMPOSITION:
--  (same original physical step -> tissue fine history ->
--   surviving original native bond endpoints -> coarse history).
-- It works for EVERY source-native PositiveBond and EVERY action history.
-- No function extensionality and no generic invented field state.
allOriginalBondPatternsCommuteAfterPhysicalHistory :
  (model : Physical.SourcePhysicalTissueSimulation)
  (actions : List Bio.Intervention)
  (state : Physical.PhysicalState model)
  (edge : Grid.PositiveBond) →
  Grid.fineJunctionPair
    (Physical.tissueReadout model
      (Physical.physicalTrace model actions state)) edge
  ≡
  Grid.coarseJunctionPair
    (Tissue.fullCoarseRun actions
      (Bio.spatialProject (Physical.tissueReadout model state))) edge
allOriginalBondPatternsCommuteAfterPhysicalHistory
  model actions state edge =
  cong₂ _,_
    (Tissue.junctionAgreement
      (Physical.tissueReadout model
        (Physical.physicalTrace model actions state))
      (Tissue.fullCoarseRun actions
        (Bio.spatialProject (Physical.tissueReadout model state)))
      (Physical.physicalHistoryProjectsToAll54Bonds
        model actions state)
      (Grid.bondStart edge))
    (Tissue.junctionAgreement
      (Physical.tissueReadout model
        (Physical.physicalTrace model actions state))
      (Tissue.fullCoarseRun actions
        (Bio.spatialProject (Physical.tissueReadout model state)))
      (Physical.physicalHistoryProjectsToAll54Bonds
        model actions state)
      (Grid.bondEnd edge))

-- The geometric ORGANIZING RESPONSE itself commutes at all 27 original
-- voxels. This is stronger than comparing final morphology alone.
originalOrganizingResponseCommutesAfterPhysicalHistory :
  (model : Physical.SourcePhysicalTissueSimulation)
  (actions : List Bio.Intervention)
  (state : Physical.PhysicalState model)
  (voxel : Cube.Ternary27Point) →
  Tissue.fineMorphogenicResponse
    (Physical.tissueReadout model
      (Physical.physicalTrace model actions state)) voxel
  ≡
  Tissue.coarseMorphogenicResponse
    (Tissue.fullCoarseRun actions
      (Bio.spatialProject (Physical.tissueReadout model state))) voxel
originalOrganizingResponseCommutesAfterPhysicalHistory
  model actions state voxel =
  Tissue.responseAgreement
    (Physical.tissueReadout model
      (Physical.physicalTrace model actions state))
    (Tissue.fullCoarseRun actions
      (Bio.spatialProject (Physical.tissueReadout model state)))
    (Physical.physicalHistoryProjectsToAll54Bonds model actions state)
    voxel

-- Selected finite BOOLEAN basin property after an arbitrary physical
-- history. Idempotence belongs to the native tissue SIGNAL OPERATOR; this
-- does not prove the physical PNP solver returns to the same state.
selectedNativeSignalBasinAfterPhysicalHistory :
  (model : Physical.SourcePhysicalTissueSimulation)
  (actions : List Bio.Intervention)
  (state : Physical.PhysicalState model)
  (voxel : Cube.Ternary27Point) →
  Tissue.fullFineStep Bio.signal
    (Tissue.fullFineStep Bio.signal
      (Physical.tissueReadout model
        (Physical.physicalTrace model actions state))) voxel
  ≡
  Tissue.fullFineStep Bio.signal
    (Physical.tissueReadout model
      (Physical.physicalTrace model actions state)) voxel
selectedNativeSignalBasinAfterPhysicalHistory model actions state voxel =
  Tissue.allNeighbourSignalIdempotentAt
    (Physical.tissueReadout model
      (Physical.physicalTrace model actions state)) voxel

------------------------------------------------------------------------
-- Q2 Filsinger: source-indexed NUMERICAL face identification cannot be
-- guessed from visual similarity with a biological original bond.
-- The original mesh membership is carried by MeshSelectedCayleyFace;
-- a user-supplied original-coordinate map must identify both endpoint IDs.
------------------------------------------------------------------------

record NativeBondToSelectedNumericalFace : Set where
  field
    nativeBond : Grid.PositiveBond
    originalNodeID : Cube.Ternary27Point → Nat
    selectedNumericalFace : Cayley.MeshSelectedCayleyFace
    sourceIDMatchesNative :
      Face.DirectedFace.source
        (Cayley.IndexedCayleyFace.originalFace
          (Cayley.MeshSelectedCayleyFace.selected selectedNumericalFace))
      ≡ originalNodeID (Grid.bondStart nativeBond)
    targetIDMatchesNative :
      Face.DirectedFace.target
        (Cayley.IndexedCayleyFace.originalFace
          (Cayley.MeshSelectedCayleyFace.selected selectedNumericalFace))
      ≡ originalNodeID (Grid.bondEnd nativeBond)

open NativeBondToSelectedNumericalFace

nativeBondCayleyPrimitiveSourceID :
  (weld : NativeBondToSelectedNumericalFace) →
  Frame.LocalPrimitive.firstID
    (Cayley.indexedCayleyPrimitive
      (Cayley.MeshSelectedCayleyFace.selected
        (selectedNumericalFace weld)))
  ≡ originalNodeID weld (Grid.bondStart (nativeBond weld))
nativeBondCayleyPrimitiveSourceID weld =
  trans
    (Cayley.indexedSourceIDExact
      (Cayley.MeshSelectedCayleyFace.selected
        (selectedNumericalFace weld)))
    (sourceIDMatchesNative weld)

nativeBondCayleyPrimitiveTargetID :
  (weld : NativeBondToSelectedNumericalFace) →
  Frame.LocalPrimitive.secondID
    (Cayley.indexedCayleyPrimitive
      (Cayley.MeshSelectedCayleyFace.selected
        (selectedNumericalFace weld)))
  ≡ originalNodeID weld (Grid.bondEnd (nativeBond weld))
nativeBondCayleyPrimitiveTargetID weld =
  trans
    (Cayley.indexedTargetIDExact
      (Cayley.MeshSelectedCayleyFace.selected
        (selectedNumericalFace weld)))
    (targetIDMatchesNative weld)

-- An identification of IDs is NOT a physical E/H/polarization projection.
-- Maxwell constitutive laws, measured BH4 rates, field/matter stress,
-- source-work balance, SI units and real device/organism identity remain
-- external proof/evidence obligations. Do NOT infer either from this type.

------------------------------------------------------------------------
-- Small separate work firewall: exact finite flux/amount conservation
-- is reused without identifying the selected Boolean field with PNP energy.
------------------------------------------------------------------------

originalConservativeTransportStillRequiresItsOwnCarrier :
  (direction : Diffusion.FluxDirection)
  (state : Diffusion.IonPairState) →
  Diffusion.totalAmount (Diffusion.transport direction state)
    ≡ Diffusion.totalAmount state
originalConservativeTransportStillRequiresItsOwnCarrier =
  Diffusion.transportConservesAmount
