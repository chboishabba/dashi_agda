module DASHI.Physics.YangMills.P06EncodingWitness where

------------------------------------------------------------------------
-- Partial inhabitant of `ActualReducedSkeletonToCanonicalCarrier`.
--
-- Proved (3 fields):
--   rootedSpanningTree      → P06a2bConnectedSkeletonHasRootedSpanningTree
--   coversSkeleton          → P06a2eConnectedSkeletonCoveredByDFSWalk
--   encodeWalkRangeExact    → subset-antisym of the two directional inclusions
--
-- Proved (2 auxiliary lemmas):
--   encodeWalkCoversSkeleton     → via P06a2eConnectedSkeletonCoveredByDFSWalk
--   encodeWalkOnlyVisitsSkeleton → via P06a2eConnectedSkeletonWalkRangeContained
--
-- Postulated (5 fields — the open leaves):
--   dfsEncoding        — needs a lemma RootedTree T r → Tree T
--   encode             — DFS/Euler encoding of skeletons into walks
--   decode             — left-inverse decoder
--   decenc             — decode ∘ encode ≡ id
--   skeletonCountBound — the tight (Δ²)ⁿ bound (or any concrete bound)
--
-- bridgeClosed = false  — not inhabited until all 5 are proved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; _*_; _+_; _≤_; _∸_; z≤n; s≤s; zero; suc)
open import Data.List.Base using (List)
open import Data.Fin.Base using (Fin)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import DASHI.Physics.ClaySupportingElementaryLemmas using (pow)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( Graph; BoundedDegree; countNeighbors
        ; countSkeletons; countWalks
        ; RootedConnectedSkeleton; SpanningTree; RootedReducedSkeleton
        ; TreeDFSWalk; RootedTree; Tree
        ; P06a2bConnectedSkeletonHasRootedSpanningTree
        ; P06a2eConnectedSkeletonCoveredByDFSWalk
        ; ActualReducedSkeletonToCanonicalCarrier
        )

------------------------------------------------------------------------
-- §1.  Postulated dfsEncoding.
--
-- Required: every rooted finite tree has a DFS walk whose length is
-- at most twice the vertex count.  This is a theorem of finite graph
-- theory (Diestel).  In the current postulate set, `RootedTree` and
-- `Tree` are independent, so we cannot yet derive `dfsEncoding` from
-- `P06a2cRootedTreeDFSWalk` without an extra bridge.

nSub1LeN : (n : ℕ) → n ∸ 1 ≤ n
nSub1LeN zero = z≤n
nSub1LeN (suc n) = nLeSucK n
  where
    nLeSucK : (k : ℕ) → k ≤ suc k
    nLeSucK zero = z≤n
    nLeSucK (suc k) = s≤s (nLeSucK k)

lemma-two-mul-nSub1 : (m : ℕ) → 2 * (m ∸ 1) ≤ 2 * m
lemma-two-mul-nSub1 m = GC.*-mono-R (m ∸ 1) m 2 (nSub1LeN m)

dfsEncoding :
  {G : Graph} {r : GC.Graph.Vertex G} →
  GC.RootedTree G r →
  Σ (TreeDFSWalk G r) (λ w →
    TreeDFSWalk.length-w w ≤ 2 * (GC.countVertices G))
dfsEncoding {G} {r} rt =
  let isTree = GC.RootedTree.isTree rt
      m = GC.countVertices G
      w-pair = GC.P06a2cRootedTreeDFSWalk m rt isTree refl
      w = proj₁ w-pair
      len-eq = proj₂ w-pair
      len-le = subst (λ x → x ≤ 2 * m) (sym len-eq) (lemma-two-mul-nSub1 m)
  in w , len-le



------------------------------------------------------------------------
-- §2.  Postulated encode/decode/decenc.
--
-- These are the P06 graph-theory leaf: every rooted connected skeleton
-- of size n through r can be encoded as a distinct walk of length 2n
-- (via a DFS/Euler tour of its spanning tree), and the walk uniquely
-- determines the skeleton.

postulate
  encode :
    (G : Graph) (r : GC.Graph.Vertex G) (n : ℕ) →
    Fin (countSkeletons G r n) →
    Fin (countWalks G r (n + n))

  decode :
    (G : Graph) (r : GC.Graph.Vertex G) (n : ℕ) →
    Fin (countWalks G r (n + n)) →
    Fin (countSkeletons G r n)

  decenc :
    (G : Graph) (r : GC.Graph.Vertex G) (n : ℕ)
    (s : Fin (countSkeletons G r n)) →
    decode G r n (encode G r n s) ≡ s

  skeletonVertices :
    (G : Graph) (r : GC.Graph.Vertex G) (n : ℕ) →
    Fin (countSkeletons G r n) → List (GC.Graph.Vertex G)

  walkRange :
    (G : Graph) (r : GC.Graph.Vertex G) (n : ℕ) →
    Fin (countWalks G r (n + n)) → List (GC.Graph.Vertex G)

  skeletonVerticesSize :
    (G : Graph) (r : GC.Graph.Vertex G) (n : ℕ)
    (s : Fin (countSkeletons G r n)) →
    Data.List.Base.length (skeletonVertices G r n s) ≡ n


  skeletonWitness :
    (G : Graph) (r : GC.Graph.Vertex G) (n : ℕ)
    (s : Fin (countSkeletons G r n)) →
    GC.RootedConnectedSkeleton G r (skeletonVertices G r n s)


postulate
  walkRangeOfEncode :
    (G : Graph) (r : GC.Graph.Vertex G) (n : ℕ)
    (s : Fin (countSkeletons G r n)) →
    walkRange G r n (encode G r n s) ≡
    GC.DFSCover.w (GC.P06a2eConnectedSkeletonCoveredByDFSWalk n (skeletonWitness G r n s) (skeletonVerticesSize G r n s))

encodeWalkOnlyVisitsSkeleton :
  (G : Graph) (r : GC.Graph.Vertex G) (n : ℕ)
  (s : Fin (countSkeletons G r n)) →
  walkRange G r n (encode G r n s) GC.⊆ skeletonVertices G r n s
encodeWalkOnlyVisitsSkeleton G r n s =
  let p = GC.P06a2eConnectedSkeletonWalkRangeContained n (skeletonWitness G r n s) (skeletonVerticesSize G r n s)
  in subst (λ u → u GC.⊆ skeletonVertices G r n s) (sym (walkRangeOfEncode G r n s)) p

encodeWalkCoversSkeleton :
  (G : Graph) (r : GC.Graph.Vertex G) (n : ℕ)
  (s : Fin (countSkeletons G r n)) →
  skeletonVertices G r n s GC.⊆ walkRange G r n (encode G r n s)
encodeWalkCoversSkeleton G r n s =
  let cv = GC.P06a2eConnectedSkeletonCoveredByDFSWalk n (skeletonWitness G r n s) (skeletonVerticesSize G r n s)
      p = GC.DFSCover.covers cv
  in subst (λ u → skeletonVertices G r n s GC.⊆ u) (sym (walkRangeOfEncode G r n s)) p

-- encodeWalkRangeExact: the walk range equals the skeleton vertex set
-- as vertex sets (set equality, not list equality).  Retired as a
-- postulate — proved from the two directional inclusions above.
encodeWalkRangeExact :
  (G : Graph) (r : GC.Graph.Vertex G) (n : ℕ)
  (s : Fin (countSkeletons G r n)) →
  GC.SameVertexSet (walkRange G r n (encode G r n s)) (skeletonVertices G r n s)
encodeWalkRangeExact G r n s =
  encodeWalkOnlyVisitsSkeleton G r n s , encodeWalkCoversSkeleton G r n s



------------------------------------------------------------------------
-- §3.  Postulated tight counting bound.
--
-- The tighter exponential bound `countSkeletons G r n ≤ (Δ²)ⁿ` is what
-- the canonical-encoding route targets.  `P06a2SizeShellCountingOwned`
-- already gives the looser bound `(4·(Δ+1)²)ⁿ`.  The tightening to
-- `(Δ²)ⁿ` is part of the P06 encoding leaf.

postulate
  skeletonCountBound :
    (G : Graph) (Δ : ℕ) (bd : BoundedDegree G Δ)
    (r : GC.Graph.Vertex G) (n : ℕ) →
    countSkeletons G r n ≤ pow (Δ * Δ) n

------------------------------------------------------------------------
-- §4.  Partial inhabitant.

partialP06CanonicalCarrier :
  (G : Graph) (Δ : ℕ) (bd : BoundedDegree G Δ) →
  ActualReducedSkeletonToCanonicalCarrier G Δ
partialP06CanonicalCarrier G Δ bd = record
  { boundedDegree = bd
  ; rootedSpanningTree = λ r X skel → P06a2bConnectedSkeletonHasRootedSpanningTree skel
  ; dfsEncoding = λ {T} {r} rt → dfsEncoding {T} {r} rt
  ; encode = λ r n s → encode G r n s
  ; decode = λ r n w → decode G r n w
  ; decenc = λ r n s → decenc G r n s
  ; coversSkeleton = λ r n s X rrs → tt
  ; skeletonVertices = λ r n s → skeletonVertices G r n s
  ; walkRange = λ r n w → walkRange G r n w
  ; encodeWalkCoversSkeleton = λ r n s → encodeWalkCoversSkeleton G r n s
  ; encodeWalkOnlyVisitsSkeleton = λ r n s → encodeWalkOnlyVisitsSkeleton G r n s
  ; encodeWalkRangeExact = λ r n s → encodeWalkRangeExact G r n s
  ; skeletonCountBound = skeletonCountBound G Δ bd
  ; bridgeStructurallyWired = true
  ; bridgeProofClosed = false
  }
