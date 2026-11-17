module DASHI.Physics.Motors.SmithFilsingerIndexedCayleyFaceWeldExact where

-- F13/F10 source-first SAME-EDGE weld:
-- the existing indexed DirectedFace is the ONLY source of endpoint IDs.
-- Reuse the original rational Cayley 2x2 implicit-midpoint proofs and
-- the previous all-N interleaved-source dynamic reachability theorem.
--
-- IMPORTANT physical distinction: the selection of actual electromagnetic
-- E/H or polarization state coordinates for a geometric DirectedFace
-- still requires the owner's field/face projection certificate.
-- This result does NOT infer that a physical boundary face is a curl edge.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)

import DASHI.Physics.Motors.SmithFilsingerIndexedFaceIncidenceExact as Indexed
import DASHI.Physics.Motors.SmithFilsingerLocalCausalADEFrameExact as Frame
import DASHI.Physics.Motors.SmithFilsingerLocalCausalADEReachExact as Reach
import DASHI.Physics.Motors.SmithFilsingerLocalCayleyZeroWeldExact as Cayley
import DASHI.Physics.Motors.SmithFilsingerLocalCayleyMidpointExact as Midpoint

-- A selected existing face, two genuinely distinct state IDs,
-- and certified midpoint coefficients for that SAME numerical edge.
-- Neither an arbitrary second face nor an invented energy source is
-- permitted through this record.
record IndexedCayleyFace : Set where
  field
    originalFace : Indexed.DirectedFace
    distinctEndpoints :
      Indexed.sameID (Indexed.DirectedFace.source originalFace)
        (Indexed.DirectedFace.target originalFace) ≡ false
    halfStep : Midpoint.CertifiedHalfStep

open IndexedCayleyFace

indexedCayleyEdge : IndexedCayleyFace → Cayley.DistinctCayleyEdge
indexedCayleyEdge e = record
  { firstID = Indexed.DirectedFace.source (originalFace e)
  ; secondID = Indexed.DirectedFace.target (originalFace e)
  ; distinct = distinctEndpoints e
  ; coefficients = Midpoint.CertifiedHalfStep.cayley (halfStep e)
  }

-- The actual old frame operator now updates exactly the two IDs carried
-- by ONE original indexed face, rather than freshly supplied Nat IDs.
indexedCayleyPrimitive :
  IndexedCayleyFace → Frame.LocalPrimitive ℚ
indexedCayleyPrimitive e =
  Cayley.sameCayleyPrimitive
    (Indexed.DirectedFace.source (originalFace e))
    (Indexed.DirectedFace.target (originalFace e))
    (Midpoint.CertifiedHalfStep.cayley (halfStep e))

-- The selected old primitive carries exactly the same source and
-- target IDs as the original DirectedFace. This is the essential
-- source-object identity, not a separate nominal face reference.
indexedSourceIDExact :
  (e : IndexedCayleyFace) →
  Frame.LocalPrimitive.firstID (indexedCayleyPrimitive e)
    ≡ Indexed.DirectedFace.source (originalFace e)
indexedSourceIDExact e = refl

indexedTargetIDExact :
  (e : IndexedCayleyFace) →
  Frame.LocalPrimitive.secondID (indexedCayleyPrimitive e)
    ≡ Indexed.DirectedFace.target (originalFace e)
indexedTargetIDExact e = refl

indexedGuardedSamePrimitive :
  (e : IndexedCayleyFace) →
  Reach.GuardedPrimitive.primitive
    (Cayley.guardedDistinctCayleyEdge (indexedCayleyEdge e))
      ≡ indexedCayleyPrimitive e
indexedGuardedSamePrimitive e = refl

indexedCayleyZero :
  (e : IndexedCayleyFace) →
  Reach.ZeroPreserving 0ℚ (indexedCayleyPrimitive e)
indexedCayleyZero e =
  Cayley.sameCayleyZeroPreserving
    (Indexed.DirectedFace.source (originalFace e))
    (Indexed.DirectedFace.target (originalFace e))
    (Midpoint.CertifiedHalfStep.cayley (halfStep e))

indexedCayleyEvent :
  IndexedCayleyFace → Reach.LocalEvent ℚ 0ℚ
indexedCayleyEvent e =
  Reach.propagate
    (Cayley.guardedDistinctCayleyEdge (indexedCayleyEdge e))

-- The FIRST and SECOND actual two-coordinate outputs satisfy the SAME
-- existing implicit midpoint equations with no new mathematical axiom.
indexedFaceFirstMidpoint :
  (e : IndexedCayleyFace) (x y : ℚ) →
  Cayley.sameCayleyFirst (Midpoint.CertifiedHalfStep.cayley (halfStep e)) x y
    - Midpoint.CertifiedHalfStep.p (halfStep e)
      * Cayley.sameCayleySecond
        (Midpoint.CertifiedHalfStep.cayley (halfStep e)) x y
    ≡ x + Midpoint.CertifiedHalfStep.p (halfStep e)
        * y
indexedFaceFirstMidpoint e x y =
  Midpoint.sameCayleyFirstMidpoint (halfStep e) x y

indexedFaceSecondMidpoint :
  (e : IndexedCayleyFace) (x y : ℚ) →
  Cayley.sameCayleySecond (Midpoint.CertifiedHalfStep.cayley (halfStep e)) x y
    - Midpoint.CertifiedHalfStep.r (halfStep e)
      * Cayley.sameCayleyFirst
        (Midpoint.CertifiedHalfStep.cayley (halfStep e)) x y
    ≡ y + Midpoint.CertifiedHalfStep.r (halfStep e)
        * x
indexedFaceSecondMidpoint e x y =
  Midpoint.sameCayleySecondMidpoint (halfStep e) x y

-- A tagged external source event is admitted only as a separate
-- injection, not silently through a passive Cayley face stage.
indexedFaceWithSource :
  Reach.SourceOwner → Nat → (ℚ → ℚ) →
  IndexedCayleyFace → List (Reach.LocalEvent ℚ 0ℚ)
indexedFaceWithSource owner sourceID change e =
  Reach.injectAt owner sourceID change ∷
  indexedCayleyEvent e ∷ []

indexedFaceSourceCone :
  (owner : Reach.SourceOwner) (sourceID : Nat)
  (change : ℚ → ℚ) (e : IndexedCayleyFace)
  (s : Frame.State ℚ) (R : Nat → Set) →
  Reach.OutsideZero 0ℚ s R →
  Reach.OutsideZero 0ℚ
    (Reach.runEvents (indexedFaceWithSource owner sourceID change e) s)
    (Reach.reachEvents (indexedFaceWithSource owner sourceID change e) R)
indexedFaceSourceCone owner sourceID change e s R premise =
  Reach.noSignalOutsideInterleavedSourceCone
    0ℚ (indexedFaceWithSource owner sourceID change e) s R premise

-- A face record alone can be manufactured. This companion requires
-- a CONSTRUCTIVE membership proof in the SAME original mesh's face list.
-- It does not accept a merely equivalent face ID from a second mesh.
data FaceMember (face : Indexed.DirectedFace) :
  List Indexed.DirectedFace → Set where
  memberHere :
    ∀ {faces} → FaceMember face (face ∷ faces)
  memberThere :
    ∀ {other faces} → FaceMember face faces →
      FaceMember face (other ∷ faces)

record MeshSelectedCayleyFace : Set where
  field
    mesh : Indexed.IndexedMesh
    selected : IndexedCayleyFace
    selectedReallyOccurs :
      FaceMember (originalFace selected)
        (Indexed.IndexedMesh.faces mesh)

open MeshSelectedCayleyFace

meshSelectedCayleyEvent :
  MeshSelectedCayleyFace → Reach.LocalEvent ℚ 0ℚ
meshSelectedCayleyEvent chosen =
  indexedCayleyEvent (selected chosen)

meshSelectedFaceMidpointFirst :
  (chosen : MeshSelectedCayleyFace) (x y : ℚ) →
  Cayley.sameCayleyFirst
      (Midpoint.CertifiedHalfStep.cayley (halfStep (selected chosen))) x y
    - Midpoint.CertifiedHalfStep.p (halfStep (selected chosen))
      * Cayley.sameCayleySecond
        (Midpoint.CertifiedHalfStep.cayley (halfStep (selected chosen))) x y
    ≡ x + Midpoint.CertifiedHalfStep.p (halfStep (selected chosen)) * y
meshSelectedFaceMidpointFirst chosen x y =
  indexedFaceFirstMidpoint (selected chosen) x y

meshSelectedFaceMidpointSecond :
  (chosen : MeshSelectedCayleyFace) (x y : ℚ) →
  Cayley.sameCayleySecond
      (Midpoint.CertifiedHalfStep.cayley (halfStep (selected chosen))) x y
    - Midpoint.CertifiedHalfStep.r (halfStep (selected chosen))
      * Cayley.sameCayleyFirst
        (Midpoint.CertifiedHalfStep.cayley (halfStep (selected chosen))) x y
    ≡ y + Midpoint.CertifiedHalfStep.r (halfStep (selected chosen)) * x
meshSelectedFaceMidpointSecond chosen x y =
  indexedFaceSecondMidpoint (selected chosen) x y

-- Membership and distinct endpoints are actual propositions with
-- checked constructors. Their presence does NOT provide SI calibration,
-- atmospheric forcing or a signed integrated Poynting face measurement.

-- Still OPEN: indexed electric/magnetic face-cochain identification,
-- physical propagation distance and timing, boundary normal Poynting
-- trace to actual receiver V*I, and independent source replenishment.
