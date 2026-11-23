module DASHI.Analysis.RHHyperfabricKTimeTransportedSpatialIntertwinerExact where

-- Original owners (reuse; do not construct competing carriers):
-- Foundations/Base369Ternary27HypervoxelFabricGeometryExact:
--   27-site P3^3, genuine (P3^3)^3 = P3^9 with 19,683 points.
-- Moonshine/Base369PeriodicTernaryTorusPathRestrictionBidiExact:
--   SAME 9-trit carrier, distinct periodic C3^9 adjacency.
-- Moonshine/Base369Ternary27SignedSymmetryMonsterIntertwinerExact:
--   the fixed P3 graph REFLECTION intertwiner k <-> -k, already paid.
-- Analysis/RHFourWindowC26NativeHyperfabricSquareExact:
--   true original grade C26 Singer action and retained orientation.
-- Information/PNFHistoryTimeHyperfabricDeltaExact / Reasoning
-- HistoryTimeIndexedConsumerFibreExact: original history/time owner.
-- This source defines honest k-TRANSPORTED adjacency, *not*
-- fixed-graph Singer symmetry. Agda kernel NOT executed here.
--
-- Only stage k changes in advanceRefinement; real physical time t
-- is a different type. A time-evolution source is NOT constructed.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Bool using (Bool)
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Analysis.RHFourWindowC26NativeHyperfabricSquareExact as C26
import DASHI.Unified.HyperfabricPunctured27Projective13OrientationExact as Projective
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Reflection
import DASHI.Moonshine.Base369PeriodicTernaryTorusPathRestrictionBidiExact as Periodic
import DASHI.Information.PNFHistoryTimeHyperfabricDeltaExact as Historical

Point9 : Set
Point9 = Geometry.TernaryHyperformalPoint

-- Nonidentity grade permutation applied INDEPENDENTLY to all three
-- ORIGINAL voxels (interaction, appraisal A, appraisal B).
gradeMove9 : Point9 → Point9
gradeMove9 (Geometry.ternaryHyperformalPoint interaction appA appB) =
  Geometry.ternaryHyperformalPoint
    (C26.gradeOrder26 interaction)
    (C26.gradeOrder26 appA)
    (C26.gradeOrder26 appB)

iterateGrade9 : Nat → Point9 → Point9
iterateGrade9 zero x = x
iterateGrade9 (suc k) x = gradeMove9 (iterateGrade9 k x)

-- A time-indexed base adjacency is an INPUT from the original source,
-- and is not assumed invariant, frozen, or physically supplied.
-- Constructor retains the original edge proof and both original
-- endpoint coordinates even where the transported chart looks different.
data KTimeTransportedEdge
  (Time : Set)
  (sourceEdgeAt : Time → Point9 → Point9 → Set)
  (t : Time) (k : Nat) : Point9 → Point9 → Set where
  fromOriginalEdge : ∀ {a b : Point9} →
    sourceEdgeAt t a b →
    KTimeTransportedEdge Time sourceEdgeAt t k
      (iterateGrade9 k a) (iterateGrade9 k b)

-- REAL refinement action: one nonidentity Singer grade move and a
-- new k-index. Holds for EVERY source time and every source adjacency
-- family, because the source is retained, not assumed equal to its image.
refinementIntertwines :
  ∀ {Time : Set}
    {sourceEdgeAt : Time → Point9 → Point9 → Set}
    {t : Time} {k : Nat} {p q : Point9} →
  KTimeTransportedEdge Time sourceEdgeAt t k p q →
  KTimeTransportedEdge Time sourceEdgeAt t (suc k)
    (gradeMove9 p) (gradeMove9 q)
refinementIntertwines (fromOriginalEdge sourceProof) =
  fromOriginalEdge sourceProof

-- Concrete original nonperiodic P3^9 source, not a new 27-state
-- fiction and not the distinct torus adjacency.
originalPathAt : {Time : Set} →
  Time → Point9 → Point9 → Set
originalPathAt t p q = Geometry.HyperformalAdjacent p q

nativePathIntertwines :
  ∀ {Time : Set} {t : Time} {k : Nat} {p q : Point9} →
  KTimeTransportedEdge Time originalPathAt t k p q →
  KTimeTransportedEdge Time originalPathAt t (suc k)
    (gradeMove9 p) (gradeMove9 q)
nativePathIntertwines = refinementIntertwines

-- The original periodic torus is a distinct time-indexed adjacency
-- producer, but the SAME general transport theorem applies.
originalTorusAt : {Time : Set} →
  Time → Point9 → Point9 → Set
originalTorusAt t p q = Periodic.TorusHyperformalAdjacent p q

nativeTorusIntertwines :
  ∀ {Time : Set} {t : Time} {k : Nat} {p q : Point9} →
  KTimeTransportedEdge Time originalTorusAt t k p q →
  KTimeTransportedEdge Time originalTorusAt t (suc k)
    (gradeMove9 p) (gradeMove9 q)
nativeTorusIntertwines = refinementIntertwines

-- The pre-existing spatial reflection proof is about fixed P3^3
-- adjacency. This remains separately imported and constructive.
alreadyOwnedReflectionPreservesUntransportedSpatialGraph :
  ∀ {p q} → Geometry.HypervoxelAdjacent p q →
  Geometry.HypervoxelAdjacent (Reflection.flipX p) (Reflection.flipX q)
alreadyOwnedReflectionPreservesUntransportedSpatialGraph =
  Reflection.flipXPreservesAdjacency

-- A history/time/k-indexed section keeps source and consumer provenance
-- separate. It does NOT assume time is refinement stage, nor that
-- parity/orientation is the same type as an RH analytic sign/residual.
record KTimeSourceFrame
  (History Time Sign Residual Mode Observation Version : Set) : Set where
  constructor kTimeSourceFrame
  field
    history : History
    physicalTime : Time
    refinement : Nat
    consumerVersion : Version
    rhSign : Sign
    rhResidual : Residual
    rhMode : Mode
    observedZeroTag : Observation
    originalNineTritSource : Point9
open KTimeSourceFrame public

viewAt :
  ∀ {H T S R M O V : Set} →
  KTimeSourceFrame H T S R M O V → Point9
viewAt f = iterateGrade9 (refinement f) (originalNineTritSource f)

-- The original typed 13-axis+Bool codec, with centre allowed to
-- remain 'nothing'. A 9D hyperfabric can contain zero voxels.
originalInteractionOrientation :
  ∀ {H T S R M O V : Set} →
  KTimeSourceFrame H T S R M O V →
  Maybe C26.Code26
originalInteractionOrientation f =
  Projective.encode
    (Geometry.interactionVoxel (originalNineTritSource f))

advanceRefinement :
  ∀ {H T S R M O V : Set} →
  KTimeSourceFrame H T S R M O V →
  KTimeSourceFrame H T S R M O V
advanceRefinement
  (kTimeSourceFrame h t k version sign residual mode observation src) =
  kTimeSourceFrame h t (suc k) version sign residual mode observation src

refinementChangesView :
  ∀ {H T S R M O V : Set}
    (f : KTimeSourceFrame H T S R M O V) →
  viewAt (advanceRefinement f) ≡ gradeMove9 (viewAt f)
refinementChangesView
  (kTimeSourceFrame h t k version sign residual mode observation src) = refl

refinementPreservesPhysicalTime :
  ∀ {H T S R M O V : Set}
    (f : KTimeSourceFrame H T S R M O V) →
  physicalTime (advanceRefinement f) ≡ physicalTime f
refinementPreservesPhysicalTime
  (kTimeSourceFrame h t k version sign residual mode observation src) = refl

refinementPreservesSource :
  ∀ {H T S R M O V : Set}
    (f : KTimeSourceFrame H T S R M O V) →
  originalNineTritSource (advanceRefinement f) ≡ originalNineTritSource f
refinementPreservesSource
  (kTimeSourceFrame h t k version sign residual mode observation src) = refl

refinementPreservesRHSign :
  ∀ {H T S R M O V : Set}
    (f : KTimeSourceFrame H T S R M O V) →
  rhSign (advanceRefinement f) ≡ rhSign f
refinementPreservesRHSign
  (kTimeSourceFrame h t k version sign residual mode observation src) = refl

refinementPreservesRHResidual :
  ∀ {H T S R M O V : Set}
    (f : KTimeSourceFrame H T S R M O V) →
  rhResidual (advanceRefinement f) ≡ rhResidual f
refinementPreservesRHResidual
  (kTimeSourceFrame h t k version sign residual mode observation src) = refl

refinementPreservesObservation :
  ∀ {H T S R M O V : Set}
    (f : KTimeSourceFrame H T S R M O V) →
  observedZeroTag (advanceRefinement f) ≡ observedZeroTag f
refinementPreservesObservation
  (kTimeSourceFrame h t k version sign residual mode observation src) = refl

refinementPreservesVersion :
  ∀ {H T S R M O V : Set}
    (f : KTimeSourceFrame H T S R M O V) →
  consumerVersion (advanceRefinement f) ≡ consumerVersion f
refinementPreservesVersion
  (kTimeSourceFrame h t k version sign residual mode observation src) = refl

-- OPEN: actual physical time step T_{t,k}, nonidentity source-time
-- commutator, actual RH zeta zeros/μ/FarExact/compensation response,
-- original nine-DOF H07 pivot/metric and any analytic completion.
