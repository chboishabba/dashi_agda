module DASHI.Physics.Motors.SmithFilsingerFullVectorIndexedFaceSampleExact where

-- F10-INC 3-component E×B face-flux sample + orientation reversal.
-- Actual pointwise Maxwell jet is consumed, not substituted with a
-- freely chosen unrelated phasor. Reuses original C3 real field solver,
-- the KSW668 3-vector jet and strict per-face ID mesh from F10-INC.
--
-- This is an algebraic finite face QUADRATURE SAMPLE, NOT the
-- spacetime Stokes integral of an SI electromagnetic field. The
-- extension from samples to integrated local-work receipts is OPEN.

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Plasma.KSW668FullVectorMaxwellJetExact as Vector
import DASHI.Physics.Motors.SmithFilsingerIndexedFaceIncidenceExact as Indexed
import DASHI.Physics.Motors.SmithFilsingerSignedIndexedFaceFluxExact as Signed

cross3 :
  ∀ {r} (F : C3.RealField r) →
  Vector.R3 F → Vector.R3 F → Vector.R3 F
cross3 F a b =
  Vector.r3
    (C3.add F
      (C3.multiply F (Vector.y a) (Vector.z b))
      (C3.negate F
        (C3.multiply F (Vector.z a) (Vector.y b))))
    (C3.add F
      (C3.multiply F (Vector.z a) (Vector.x b))
      (C3.negate F
        (C3.multiply F (Vector.x a) (Vector.z b))))
    (C3.add F
      (C3.multiply F (Vector.x a) (Vector.y b))
      (C3.negate F
        (C3.multiply F (Vector.y a) (Vector.x b))))

-- An actual 3-component Poynting face trace at one supplied Maxwell jet.
-- KSW668 uses normalized epsilon=mu=c=1 and magnetic B.
poyntingFaceSample :
  ∀ {r} (F : C3.RealField r) →
  Vector.R3 F → Vector.FullVectorMaxwellJet F → C3.Carrier F
poyntingFaceSample F outwardNormal jet =
  Vector.dot3 F outwardNormal
    (cross3 F (Vector.electric jet) (Vector.magnetic jet))

-- The normal's sign is not a scalar-Nat label: this theorem proves
-- that reversing the actual three-vector orientation negates E×B flux.
dotReversedNormal :
  ∀ {r} (F : C3.RealField r)
  (normal poynting : Vector.R3 F) →
  Vector.dot3 F (Vector.negate3 F normal) poynting
    ≡ C3.negate F (Vector.dot3 F normal poynting)
dotReversedNormal F normal poynting =
  R.solve 6
    (λ nx ny nz sx sy sz →
      ((((R.⊝ nx) R.⊗ sx) R.⊕ ((R.⊝ ny) R.⊗ sy))
         R.⊕ ((R.⊝ nz) R.⊗ sz))
      R.⊜
      (R.⊝ (((nx R.⊗ sx) R.⊕ (ny R.⊗ sy))
         R.⊕ (nz R.⊗ sz))))
    refl
    (Vector.x normal) (Vector.y normal) (Vector.z normal)
    (Vector.x poynting) (Vector.y poynting)
    (Vector.z poynting)
  where module R = Algebra.Solver F

poyntingNormalReversal :
  ∀ {r} (F : C3.RealField r)
  (normal : Vector.R3 F)
  (jet : Vector.FullVectorMaxwellJet F) →
  poyntingFaceSample F (Vector.negate3 F normal) jet
    ≡ C3.negate F (poyntingFaceSample F normal jet)
poyntingNormalReversal F normal jet =
  dotReversedNormal F normal
    (cross3 F (Vector.electric jet) (Vector.magnetic jet))

-- Actual FACE weights/metric must be calibrated separately. One face
-- record holds its own jet, orientation and area×time quadrature weight.
-- A per-face jet is not asserted to be a continuous global Maxwell
-- solution or the actual Filsinger field.
record SelectedFaceSamples {r : Level} (F : C3.RealField r)
  (mesh : Indexed.IndexedMesh) : Set (lsuc r) where
  field
    jet : Indexed.DirectedFace → Vector.FullVectorMaxwellJet F
    outwardSourceNormal : Indexed.DirectedFace → Vector.R3 F
    sampleWeight : Indexed.DirectedFace → C3.Carrier F

faceSampleWork :
  ∀ {r} {F : C3.RealField r} {mesh : Indexed.IndexedMesh} →
  SelectedFaceSamples F mesh →
  Indexed.DirectedFace → C3.Carrier F
faceSampleWork {F = F} samples f =
  C3.multiply F
    (SelectedFaceSamples.sampleWeight samples f)
    (poyntingFaceSample F
      (SelectedFaceSamples.outwardSourceNormal samples f)
      (SelectedFaceSamples.jet samples f))

-- This really consumes the original Maxwell pointwise Poynting identity,
-- but does not turn it into a spacetime integral by implication alone.
everySuppliedFaceJetHasPointwisePoynting :
  ∀ {r} {F : C3.RealField r} {mesh : Indexed.IndexedMesh} →
  (samples : SelectedFaceSamples F mesh)
  (f : Indexed.DirectedFace) →
  Vector.fullVectorSignedBudget (SelectedFaceSamples.jet samples f)
    ≡ C3.zero F
everySuppliedFaceJetHasPointwisePoynting samples f =
  Vector.fullVectorMaxwellPoyntingIdentity
    (SelectedFaceSamples.jet samples f)

-- Signed source/target face fluxes have exact opposite orientations
-- over ANY face list, including branched and cyclic strict meshes.
allSelectedFullVectorFaceSamplesCancel :
  ∀ {r} {F : C3.RealField r}
  (mesh : Indexed.IndexedMesh)
  (samples : SelectedFaceSamples F mesh) →
  Signed.sumField F
    (λ f → C3.add F
      (Signed.signedFaceOut F (faceSampleWork samples) f)
      (Signed.signedFaceIn F (faceSampleWork samples) f))
    (Indexed.IndexedMesh.faces mesh)
  ≡ C3.zero F
allSelectedFullVectorFaceSamplesCancel {F = F} mesh samples =
  Signed.indexedSignedFaceCancellation F mesh (faceSampleWork samples)

-- The actual F10-STOKES/F13 source operator still requires:
-- surface/time quadrature of Maxwell source fields, physical normal
-- and SI measure, ADE/ion/wind energy and signed ports; terminal V/I;
-- real soil/air/ionosphere radiation boundary, material dispersion,
-- light cone and independently replenished real natural-source input.
