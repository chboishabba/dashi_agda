module DASHI.Physics.Motors.SmithFilsingerIndexedFaceSourceWeldExact where

-- Reuse the canonical source-indexed original full-vector Maxwell-port
-- endpoint, but accept ONLY a stricter per-face-ID verified mesh.
-- No new field equation, experimental source identity or PDE admission.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.SmithFilsingerIndexedFaceIncidenceExact as Indexed
import DASHI.Physics.Motors.SmithFilsingerFiniteVolumeFaceIncidenceExact as Face
import DASHI.Physics.Motors.SmithFilsingerFiniteVolumeMaxwellBoundaryWeldExact as Old
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Weld
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port

-- All physical original source and material/port identification must
-- still be supplied by the original owner. In particular the identity
-- below is not manufactured from a numerical magnetic curl.
record SameOriginalIndexedFaceAdmission
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b) : Set₂ where
  field
    indexed : Indexed.IndexedMesh
    originalBoundary : Old.OriginalFiniteVolumeAdmission b f
    sameIndexedPhysicalMesh :
      Old.OriginalFiniteVolumeAdmission.mesh originalBoundary
        ≡ Indexed.asExistingMesh indexed

-- The source-indexed output theorem now consumes a real *indexed*
-- endpoint attribution, NOT just equal total face flux across the mesh.
indexedFaceClosesSelectedOriginalPort :
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (admission : SameOriginalIndexedFaceAdmission b f) →
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
indexedFaceClosesSelectedOriginalPort b f admission =
  Old.finiteVolumeClosesSameOriginalSignedPorts b f
    (SameOriginalIndexedFaceAdmission.originalBoundary admission)

-- The indexed mesh's conservation theorem is not a second independent
-- source law. It reuses precisely the old generic finite-volume proof.
indexedFaceExteriorConservation :
  (mesh : Indexed.IndexedMesh) →
  Face.totalExtIn (Indexed.eraseCells (Indexed.IndexedMesh.cells mesh))
    + (Face.totalDrive (Indexed.eraseCells (Indexed.IndexedMesh.cells mesh))
      + Face.totalInitial (Indexed.eraseCells (Indexed.IndexedMesh.cells mesh)))
  ≡ Face.totalExtOut (Indexed.eraseCells (Indexed.IndexedMesh.cells mesh))
    + (Face.totalLoad (Indexed.eraseCells (Indexed.IndexedMesh.cells mesh))
      + (Face.totalLoss (Indexed.eraseCells (Indexed.IndexedMesh.cells mesh))
      + Face.totalFinal (Indexed.eraseCells (Indexed.IndexedMesh.cells mesh)))
indexedFaceExteriorConservation = Indexed.indexedFaceExteriorEnergyBalance

-- F10-STOKES remains distinct: signed real Poynting face-work quadrature
-- must produce the original local law, not merely this Nat work carrier.
