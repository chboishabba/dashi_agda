module DASHI.Physics.Motors.SmithFilsingerFiniteVolumeMaxwellBoundaryWeldExact where

-- A real finite-volume/face-incidence mesh reduces to the SAME original
-- spatial-port owner. NO new Maxwell law or fictional source generator.
-- Reuse the source-indexed original historical configuration, canonical
-- all-N spatial cell, exact full-vector Maxwell jet, and face theorem.
--
-- Physical E x H surface integration, calibrated V/I and material work
-- are still independent hypotheses. Pointwise jet != integrated work.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:=_; con)

import DASHI.Physics.Motors.SmithFilsingerFiniteVolumeFaceIncidenceExact as Face
import DASHI.Physics.Motors.SmithFilsingerSpatialPortChainExact as Spatial
import DASHI.Physics.Motors.SmithFilsingerSpatialSourceBoundaryWeldExact as Boundary
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Weld
import DASHI.Physics.Motors.SmithFilsingerFullVectorPoyntingPortWeldExact as VectorPort
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port

-- The finite mesh reduces to one existing SpatialCell only AFTER every
-- cell local budget and oriented internal face receipt has been consumed.
meshAsCanonicalSpatialCell :
  (mesh : Face.OrientedFaceMesh) →
  Spatial.SpatialCell
    (Face.totalExtIn (Face.OrientedFaceMesh.cells mesh))
    (Face.totalExtOut (Face.OrientedFaceMesh.cells mesh))
meshAsCanonicalSpatialCell mesh =
  Spatial.spatialCell
    (Face.totalDrive cs)
    (Face.totalInitial cs)
    (Face.totalLoad cs)
    (Face.totalLoss cs)
    (Face.totalFinal cs)
    (Face.finiteVolumeExteriorEnergyBalance mesh)
  where
    cs = Face.OrientedFaceMesh.cells mesh

meshAsCanonicalSpatialChain :
  (mesh : Face.OrientedFaceMesh) →
  Spatial.SpatialChain
    (Face.totalExtIn (Face.OrientedFaceMesh.cells mesh))
    (Face.totalExtOut (Face.OrientedFaceMesh.cells mesh))
meshAsCanonicalSpatialChain mesh =
  Spatial.thenCell (meshAsCanonicalSpatialCell mesh)
    (Spatial.empty (Face.totalExtOut (Face.OrientedFaceMesh.cells mesh)))

-- A singleton canonical chain has list-sum tails of zero; preserve
-- the actual face totals via an explicit semiring normalization, not an
-- unjustified definitional equality (Nat n+0 is not always definitional).
meshChainInputNormalization :
  (mesh : Face.OrientedFaceMesh) →
  Face.totalExtIn (Face.OrientedFaceMesh.cells mesh)
    + (Spatial.sumDrive (meshAsCanonicalSpatialChain mesh)
      + Spatial.sumInitialStorage (meshAsCanonicalSpatialChain mesh))
  ≡ Face.totalExtIn (Face.OrientedFaceMesh.cells mesh)
    + (Face.totalDrive (Face.OrientedFaceMesh.cells mesh)
      + Face.totalInitial (Face.OrientedFaceMesh.cells mesh))
meshChainInputNormalization mesh =
  solve 3
    (λ a d u →
      a :+ ((d :+ con 0) :+ (u :+ con 0))
        := a :+ (d :+ u))
    refl (Face.totalExtIn cs) (Face.totalDrive cs)
      (Face.totalInitial cs)
  where
    cs = Face.OrientedFaceMesh.cells mesh

meshChainOutputNormalization :
  (mesh : Face.OrientedFaceMesh) →
  Face.totalExtOut (Face.OrientedFaceMesh.cells mesh)
    + (Spatial.sumUsefulLoad (meshAsCanonicalSpatialChain mesh)
      + (Spatial.sumDissipation (meshAsCanonicalSpatialChain mesh)
      + Spatial.sumFinalStorage (meshAsCanonicalSpatialChain mesh)))
  ≡ Face.totalExtOut (Face.OrientedFaceMesh.cells mesh)
    + (Face.totalLoad (Face.OrientedFaceMesh.cells mesh)
      + (Face.totalLoss (Face.OrientedFaceMesh.cells mesh)
      + Face.totalFinal (Face.OrientedFaceMesh.cells mesh)))
meshChainOutputNormalization mesh =
  solve 4
    (λ a l q u →
      a :+ ((l :+ con 0) :+ ((q :+ con 0) :+ (u :+ con 0)))
        := a :+ (l :+ (q :+ u)))
    refl (Face.totalExtOut cs) (Face.totalLoad cs)
      (Face.totalLoss cs) (Face.totalFinal cs)
  where
    cs = Face.OrientedFaceMesh.cells mesh

-- The SAME historical Maxwell/port boundary is mandatory; arbitrary mesh
-- cells do not identify a solar source by themselves. Two measured boundary
-- identities, including outgoing waves and controller work, remain open.
record OriginalFiniteVolumeAdmission
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b) : Set₂ where
  field
    mesh : Face.OrientedFaceMesh

    -- The pointwise Maxwell owner is separate from the spacetime Stokes
    -- integration and geometry; this is an explicit physical receipt.
    selectedFullVectorMaxwellFieldToFaces : Set
    actualMaxwellCellIntegration : selectedFullVectorMaxwellFieldToFaces

    sameOriginalIncomingWork :
      Face.totalExtIn (Face.OrientedFaceMesh.cells mesh)
        + (Face.totalDrive (Face.OrientedFaceMesh.cells mesh)
          + Face.totalInitial (Face.OrientedFaceMesh.cells mesh))
      ≡ (Port.MidpointTwoPortWorkWindow.naturalIncident
          (Weld.FormalFieldToPort.portWindow f)
        + Port.MidpointTwoPortWorkWindow.controllerIncident
          (Weld.FormalFieldToPort.portWindow f))
        + Port.MidpointTwoPortWorkWindow.initialStored
          (Weld.FormalFieldToPort.portWindow f)

    sameOriginalOutgoingWork :
      Face.totalExtOut (Face.OrientedFaceMesh.cells mesh)
        + (Face.totalLoad (Face.OrientedFaceMesh.cells mesh)
          + (Face.totalLoss (Face.OrientedFaceMesh.cells mesh)
          + Face.totalFinal (Face.OrientedFaceMesh.cells mesh)))
      ≡ (Port.MidpointTwoPortWorkWindow.naturalOutgoing
          (Weld.FormalFieldToPort.portWindow f)
        + Port.MidpointTwoPortWorkWindow.controllerOutgoing
          (Weld.FormalFieldToPort.portWindow f))
        + (Port.MidpointTwoPortWorkWindow.usefulWork
          (Weld.FormalFieldToPort.portWindow f)
        + (Port.MidpointTwoPortWorkWindow.internalLoss
          (Weld.FormalFieldToPort.portWindow f)
        + Port.MidpointTwoPortWorkWindow.finalStored
          (Weld.FormalFieldToPort.portWindow f)))

-- This REALLY consumes the face theorem, then the earlier source-indexed
-- original port boundary. It makes no assertion of independently measured
-- natural input, and does not equate a Maxwell jet to a Nat work scalar.
asExistingOriginalSpatialWeld :
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (m : OriginalFiniteVolumeAdmission b f) →
  Boundary.SpatialToOriginalSourcePort b f
asExistingOriginalSpatialWeld b f m =
  record
    { entry = Face.totalExtIn (Face.OrientedFaceMesh.cells mesh)
    ; exit = Face.totalExtOut (Face.OrientedFaceMesh.cells mesh)
    ; cells = meshAsCanonicalSpatialChain mesh
    ; spatialInputIsSameOriginalPort =
        trans (meshChainInputNormalization mesh)
          (OriginalFiniteVolumeAdmission.sameOriginalIncomingWork m)
    ; spatialOutputIsSameOriginalPort =
        trans (meshChainOutputNormalization mesh)
          (OriginalFiniteVolumeAdmission.sameOriginalOutgoingWork m)
    }
  where
    mesh = OriginalFiniteVolumeAdmission.mesh m

-- Same-source boundary conservation is DERIVED, not supplied as a
-- second globally asserted physical equation.
finiteVolumeClosesSameOriginalSignedPorts :
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (m : OriginalFiniteVolumeAdmission b f) →
  (Port.MidpointTwoPortWorkWindow.naturalIncident
      (Weld.FormalFieldToPort.portWindow f)
    + Port.MidpointTwoPortWorkWindow.controllerIncident
      (Weld.FormalFieldToPort.portWindow f))
    + Port.MidpointTwoPortWorkWindow.initialStored
      (Weld.FormalFieldToPort.portWindow f)
  ≡ (Port.MidpointTwoPortWorkWindow.naturalOutgoing
      (Weld.FormalFieldToPort.portWindow f)
    + Port.MidpointTwoPortWorkWindow.controllerOutgoing
      (Weld.FormalFieldToPort.portWindow f))
    + (Port.MidpointTwoPortWorkWindow.usefulWork
      (Weld.FormalFieldToPort.portWindow f)
    + (Port.MidpointTwoPortWorkWindow.internalLoss
      (Weld.FormalFieldToPort.portWindow f)
    + Port.MidpointTwoPortWorkWindow.finalStored
      (Weld.FormalFieldToPort.portWindow f)))
finiteVolumeClosesSameOriginalSignedPorts b f m =
  Boundary.spatialEnergyClosesSelectedPort b f
    (asExistingOriginalSpatialWeld b f m)

-- To promote to a genuine Maxwell 3D source operator, supply:
--  (a) physical field E/H/J and chosen constitutive law in every cell;
--  (b) a real-oriented surface/time integral mapping to each local law;
--  (c) the same face surface quadrature with opposite orientations;
--  (d) a calibrated port contour/return path (displacement current
--      matters: Ampere current is not just the H-circulation in AC);
--  (e) independently measured solar / ionospheric source work;
--  (f) physically tested, stable and causal retarded Green operator;
--  (g) material modulation, ionisation, damping and storage return.
