module DASHI.Physics.YangMills.P06ExactEnumerationEndpoint where

------------------------------------------------------------------------
-- Public, exact-length P06 endpoint.
--
-- The legacy endpoint remains at length n + n for compatibility.  This
-- module is the canonical route: its DFS tour has the natural exact length
-- 2 (n - 1), so no nonexistent graph-edge padding is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (length)
open import Data.Nat.Base using (ℕ; _*_; _∸_; _≤_)

open import DASHI.Physics.ClaySupportingElementaryLemmas using (pow)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( Graph
        ; FiniteBallEnumeration
        ; ExplicitSkeletonCandidateEnumeration
        ; CanonicalSkeletonEnumeration
        ; CanonicalBoundedNeighbourEnumeration
        ; BoundedNeighbourEnumeration
        ; CountWalksMembershipSemantics
        ; countSkeletons
        ; countWalks
        ; generatedWalkVertexLists
        )
open import DASHI.Physics.YangMills.P06ConcreteEnumerationEndpoint as Legacy
  using ( CanonicalBoundedNeighbourEnumerationWithDegree
        ; explicitSkeletonEnumerationToCanonicalEnumeration
        ; generatedWalksToMembershipIndexedWalkList
        ; boundedDegreeFromCanonicalNeighbourEnumeration
        )
open import DASHI.Physics.YangMills.P06ConstructiveSpanningTreeDFS
  using ( p06DFSWalkLength
        ; UndirectedGraphStructure
        )
open import DASHI.Physics.YangMills.P06DFSValidWalkSurface
  using ( GeneratedWalkSemanticsCompatibility
        ; pathUnionConcreteEnumerationBound
        )

------------------------------------------------------------------------
-- The only non-geometric P06 inputs.  The neighbour-count agreement is
-- carried by CanonicalBoundedNeighbourEnumerationWithDegree, because it is
-- precisely the refinement needed to derive BoundedDegree.
------------------------------------------------------------------------

record P06ConcreteCountSemantics
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  (FBE : FiniteBallEnumeration G r (n ∸ 1))
  (CBNED : CanonicalBoundedNeighbourEnumerationWithDegree G Δ)
  (skelEnum : ExplicitSkeletonCandidateEnumeration G r n FBE)
  : Set₁ where
  field
    skeletonCountAgreement :
      countSkeletons G r n ≡
      length (ExplicitSkeletonCandidateEnumeration.candidates skelEnum)

    walkCountAgreement :
      countWalks G r (p06DFSWalkLength n) ≡
      length
        (generatedWalkVertexLists {r = r} {L = p06DFSWalkLength n}
          (CanonicalBoundedNeighbourEnumeration.bounded
            (CanonicalBoundedNeighbourEnumerationWithDegree.enumeration CBNED)))

open P06ConcreteCountSemantics public

------------------------------------------------------------------------
-- Definitional compatibility for the generated membership-indexed walk
-- semantics.  Keeping this lemma here documents that arbitrary walk
-- semantics do not receive this fact for free.
------------------------------------------------------------------------

generatedWalkSemanticsCompatibility :
  ∀ {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {L : ℕ}
  (CBNE : CanonicalBoundedNeighbourEnumeration G Δ)
  (walkCount :
    countWalks G r L ≡
    length
      (generatedWalkVertexLists {r = r} {L = L}
        (CanonicalBoundedNeighbourEnumeration.bounded CBNE)))
  → GeneratedWalkSemanticsCompatibility
      (CanonicalBoundedNeighbourEnumeration.bounded CBNE)
      (generatedWalksToMembershipIndexedWalkList CBNE walkCount)
generatedWalkSemanticsCompatibility CBNE walkCount =
  record { walks-is-generated = refl }

------------------------------------------------------------------------
-- Owned exact Euler-DFS endpoint.
--
-- No DFS map, constructive tree, traversal invariant, or legacy n+n
-- padding premise is exposed.  All finite geometry is constructed by the
-- path-union DFS closure imported through pathUnionConcreteEnumerationBound.
------------------------------------------------------------------------

P06ConcreteEnumerationTheoremOwned :
  ∀ {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  (FBE : FiniteBallEnumeration G r (n ∸ 1))
  (undirected : UndirectedGraphStructure G)
  (positiveΔ : 1 ≤ Δ)
  (CBNED : CanonicalBoundedNeighbourEnumerationWithDegree G Δ)
  (skelEnum : ExplicitSkeletonCandidateEnumeration G r n FBE)
  (counts : P06ConcreteCountSemantics FBE CBNED skelEnum)
  → countSkeletons G r n ≤ pow (Δ * Δ) n
P06ConcreteEnumerationTheoremOwned
  {G = G} {Δ = Δ} FBE undirected positiveΔ CBNED skelEnum counts =
  pathUnionConcreteEnumerationBound
    (explicitSkeletonEnumerationToCanonicalEnumeration
      skelEnum
      (skeletonCountAgreement counts))
    bounded
    (generatedWalksToMembershipIndexedWalkList
      canonical
      (walkCountAgreement counts))
    (generatedWalkSemanticsCompatibility
      canonical
      (walkCountAgreement counts))
    undirected
    (boundedDegreeFromCanonicalNeighbourEnumeration CBNED)
    positiveΔ
  where
  canonical : CanonicalBoundedNeighbourEnumeration G Δ
  canonical =
    CanonicalBoundedNeighbourEnumerationWithDegree.enumeration CBNED

  bounded : BoundedNeighbourEnumeration G Δ
  bounded = CanonicalBoundedNeighbourEnumeration.bounded canonical
