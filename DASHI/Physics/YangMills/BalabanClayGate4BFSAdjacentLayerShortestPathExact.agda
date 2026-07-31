module DASHI.Physics.YangMills.BalabanClayGate4BFSAdjacentLayerShortestPathExact where

open import Agda.Builtin.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4StrongBFSParentCertificateExact as Strong

------------------------------------------------------------------------
-- Standard BFS correctness reduction.
--
-- Once the layer assignment satisfies
--
--   adjacent u v -> distance(v) <= 1 + distance(u),
--
-- induction along an arbitrary root path shows that the assigned BFS distance
-- is no larger than the path length. Combined with the exact parent path already
-- constructed in StrongBFSParentCertificate, this proves shortest-path
-- realization without a contradiction argument or classical choice.
------------------------------------------------------------------------

≤N-transitive : ∀ {left middle right} →
  Strong._≤N_ left middle → Strong._≤N_ middle right →
  Strong._≤N_ left right
≤N-transitive Strong.zero≤N right = Strong.zero≤N
≤N-transitive (Strong.suc≤N left) (Strong.suc≤N right) =
  Strong.suc≤N (≤N-transitive left right)

record AdjacentLayerUpperBound
    {Vertex : Set}
    (certificate : Strong.StrongBFSParentCertificate Vertex) : Set₁ where
  field
    adjacentAdvancesAtMostOne : ∀ {left right} →
      Strong.Adjacent certificate left right →
      Strong._≤N_
        (Strong.distance certificate right)
        (suc (Strong.distance certificate left))

open AdjacentLayerUpperBound public

pathLengthBoundsAssignedDistance :
  ∀ {Vertex}
    {certificate : Strong.StrongBFSParentCertificate Vertex} →
  AdjacentLayerUpperBound certificate →
  ∀ {vertex pathLength} →
  Strong.RootPath certificate vertex pathLength →
  Strong._≤N_ (Strong.distance certificate vertex) pathLength
pathLengthBoundsAssignedDistance {certificate = certificate}
  upper Strong.rootPath =
  subst
    (λ selectedDistance → Strong._≤N_ selectedDistance zero)
    (sym (Strong.rootDistanceZero certificate))
    Strong.zero≤N
pathLengthBoundsAssignedDistance {certificate = certificate}
  upper (Strong.extendPath path adjacent) =
  ≤N-transitive
    (adjacentAdvancesAtMostOne upper adjacent)
    (Strong.suc≤N (pathLengthBoundsAssignedDistance upper path))

asStrongShortestPathCertificate :
  ∀ {Vertex}
    {certificate : Strong.StrongBFSParentCertificate Vertex} →
  AdjacentLayerUpperBound certificate →
  Strong.StrongBFSShortestPathCertificate certificate
asStrongShortestPathCertificate upper = record
  { distanceLowerBoundForEveryPath =
      pathLengthBoundsAssignedDistance upper
  }

assignedBFSPathIsShortest :
  ∀ {Vertex}
    {certificate : Strong.StrongBFSParentCertificate Vertex}
    (upper : AdjacentLayerUpperBound certificate)
    vertex → Strong.InGraph certificate vertex →
  Strong.RootPath certificate vertex (Strong.distance certificate vertex)
assignedBFSPathIsShortest {certificate = certificate} upper vertex inGraph =
  Strong.shortestPathRealized
    (asStrongShortestPathCertificate upper) vertex inGraph

adjacentLayerUpperBoundReductionLevel : ProofLevel
adjacentLayerUpperBoundReductionLevel = machineChecked

shortestPathFromAdjacentLayerInvariantLevel : ProofLevel
shortestPathFromAdjacentLayerInvariantLevel = machineChecked

physicalPeriodicAdjacentLayerUpperBoundInputsLevel : ProofLevel
physicalPeriodicAdjacentLayerUpperBoundInputsLevel = conditional
