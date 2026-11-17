module DASHI.Physics.Motors.SmithFilsingerSignedIndexedFaceFluxExact where

-- F10-INC → signed real-field face-flux pairing. Reuse exactly the
-- original C3.RealField ring and the stricter per-cell face-ID owner.
-- A scalar face amplitude is an abstract *integrated* field-work carrier;
-- no physical E×H surface quadrature, normals, metric, Maxwell regularity,
-- endpoint voltage/current or measured solar source is constructed.
--
-- User-origin hypothesis: nonlinear differential phase control of
-- potentially replenished solar / Earth energy. No harvesting assertion.

open import Agda.Primitive using (Level)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Motors.SmithFilsingerIndexedFaceIncidenceExact as Indexed

-- Each ID is paired with a single signed work value; the source and
-- target carry its opposite orientations, not two independent numbers.
signedFaceOut :
  ∀ {r} (F : C3.RealField r) →
  (Indexed.DirectedFace → C3.Carrier F) →
  Indexed.DirectedFace → C3.Carrier F
signedFaceOut F flux face = flux face

signedFaceIn :
  ∀ {r} (F : C3.RealField r) →
  (Indexed.DirectedFace → C3.Carrier F) →
  Indexed.DirectedFace → C3.Carrier F
signedFaceIn F flux face = C3.negate F (flux face)

-- This is a signed scalar-field sum; unlike Nat work, negative Poynting
-- flux is represented as a genuine additive inverse.
sumField :
  ∀ {r} (F : C3.RealField r) {A : Set} →
  (A → C3.Carrier F) → List A → C3.Carrier F
sumField F h [] = C3.zero F
sumField F h (x ∷ xs) =
  C3.add F (h x) (sumField F h xs)

-- EVERY internal face cancels with its opposite orientation.
-- No mesh geometry restriction or accidental cancellation of unequal
-- face IDs can replace the single-face source/target identity.
signedFacePairCancels :
  ∀ {r} (F : C3.RealField r)
  (flux : Indexed.DirectedFace → C3.Carrier F)
  (face : Indexed.DirectedFace) →
  C3.add F (signedFaceOut F flux face)
    (signedFaceIn F flux face)
  ≡ C3.zero F
signedFacePairCancels F flux face =
  Algebra.realAddInverseRight F (flux face)

-- A true all-N theorem for real-field signed oriented face work.
-- The pairing uses the SAME face record once at source and target;
-- duplicate IDs or wrong endpoints are separately rejected by IndexedMesh.
signedAllFacesCancel :
  ∀ {r} (F : C3.RealField r)
  (flux : Indexed.DirectedFace → C3.Carrier F)
  (faces : List Indexed.DirectedFace) →
  sumField F
    (λ face → C3.add F (signedFaceOut F flux face)
      (signedFaceIn F flux face)) faces
    ≡ C3.zero F
signedAllFacesCancel F flux [] = refl
signedAllFacesCancel F flux (face ∷ rest) =
  trans
    (cong (λ v → C3.add F v
      (sumField F
        (λ f → C3.add F (signedFaceOut F flux f)
          (signedFaceIn F flux f)) rest))
      (signedFacePairCancels F flux face))
    (trans
      (C3.addZeroLeft F
        (sumField F
          (λ f → C3.add F (signedFaceOut F flux f)
            (signedFaceIn F flux f)) rest))
      (signedAllFacesCancel F flux rest))

-- Same selected incidence mesh, not a disconnected list of fluxes.
indexedSignedFaceCancellation :
  ∀ {r} (F : C3.RealField r)
  (mesh : Indexed.IndexedMesh)
  (calibratedFaceFlux : Indexed.DirectedFace → C3.Carrier F) →
  sumField F
    (λ face → C3.add F
      (signedFaceOut F calibratedFaceFlux face)
      (signedFaceIn F calibratedFaceFlux face))
    (Indexed.IndexedMesh.faces mesh)
  ≡ C3.zero F
indexedSignedFaceCancellation F mesh flux =
  signedAllFacesCancel F flux (Indexed.IndexedMesh.faces mesh)

-- Deliberately OPEN:
-- (1) face work really integrates (E×H)·n over one selected oriented face;
-- (2) per-volume spacetime Stokes/Faraday/Ampere and ADE/ionization losses;
-- (3) actual physical terminal V and conduction+displacement current;
-- (4) calibrated Earth/ionosphere nonstationary Green operator;
-- (5) independently replenished natural work over restored cycles.
