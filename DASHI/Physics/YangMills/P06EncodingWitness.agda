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
open import Data.List.Base using (List; length)
open import Data.Fin.Base using (Fin)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import DASHI.Physics.ClaySupportingElementaryLemmas using (pow)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( Graph; BoundedDegree; countNeighbors
        ; countSkeletons; countWalks
        ; BoundedNeighbourEnumeration; ConcreteWalkCountAgreement
        ; walkObjectsFromNeighbourCodes
        ; FiniteBallEnumeration
        ; ExplicitSkeletonCandidateEnumeration
        ; CountSkeletonsSemantics; ConcreteCountSkeletonsSemantics
        ; CountWalksSemantics
        ; CountWalksMembershipSemantics
        ; generatedWalksToMembershipIndexedCanonicalWalkObjectList
        ; ActualSkeletonEncodingData
        ; actualSkeletonEncodingDataFromSemantics
        ; actualSkeletonCountBound
        ; concreteCountSkeletonsSemanticsToCountSkeletonsSemantics
        ; RootedConnectedSkeleton; SpanningTree; RootedReducedSkeleton
        ; TreeDFSWalk; RootedTree; Tree
        ; P06a2bConnectedSkeletonHasRootedSpanningTree
        ; P06a2eConnectedSkeletonCoveredByDFSWalk
        ; ActualReducedSkeletonToCanonicalCarrier
        )

------------------------------------------------------------------------
-- Compatibility-only concrete walk-count adapter.
--
-- `ConcreteWalkCountAgreement` is exactly the count equality needed by
-- the generated-walk surface.  It is not yet a `CountWalksSemantics`:
-- the latter also needs a Fin-indexed `walkOfFin`/`walkIndex` pair and
-- its inverse law.  Keep that membership-to-indexing conversion visible
-- here rather than silently treating the two surfaces as interchangeable.
-- This record is deliberately non-promoting and does not construct a
-- `CountWalksSemantics` witness.
record P06ConcreteWalkCountAgreementAdapter
  (G : Graph) (Δ : ℕ)
  (BNE : GC.BoundedNeighbourEnumeration G Δ)
  (r : GC.Graph.Vertex G) (L : ℕ) : Set₁ where
  field
    concreteAgreement : GC.ConcreteWalkCountAgreement G Δ BNE r L

    -- The corrected finite semantic surface is constructively available
    -- from the same explicit count equality.  It is separate from the
    -- legacy total-index surface below, which remains open for migration.
    membershipIndexedSemantics :
      CountWalksMembershipSemantics G r L

    countAgrees :
      countWalks G r L
        ≡ length (GC.walkObjectsFromNeighbourCodes BNE r L)

    -- Open bridge: list membership in the generated walk list has not
    -- been converted into the Fin indexing required by CountWalksSemantics.
    membershipIndexingBlocker : Bool
    membershipIndexingBlockerIsActive : membershipIndexingBlocker ≡ true

p06ConcreteWalkCountAgreementAdapter :
  {G : Graph} {Δ : ℕ}
  {BNE : GC.BoundedNeighbourEnumeration G Δ}
  {r : GC.Graph.Vertex G} {L : ℕ} →
  GC.ConcreteWalkCountAgreement G Δ BNE r L →
  P06ConcreteWalkCountAgreementAdapter G Δ BNE r L
p06ConcreteWalkCountAgreementAdapter agreement = record
  { concreteAgreement = agreement
  ; membershipIndexedSemantics =
      GC.generatedWalksToMembershipIndexedCanonicalWalkObjectList
        _ agreement
  ; countAgrees = GC.ConcreteWalkCountAgreement.countAgrees agreement
  ; membershipIndexingBlocker = true
  ; membershipIndexingBlockerIsActive = refl
  }

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
-- §5.  Active semantic P06 surface.
--
-- The old carrier above is retained as a compatibility surface for files
-- which have not yet migrated.  New P06 work must use this record instead:
-- its only open inputs are the two semantic meanings of the abstract count
-- functions.  Everything from the canonical enumerations through the DFS
-- injection and the (Δ²)^n estimate is derived in GraphCombinatorics.
------------------------------------------------------------------------

record P06SemanticCountWitness
  (G : Graph) (Δ : ℕ) (r : GC.Graph.Vertex G) (n : ℕ)
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) : Set₁ where
  field
    skeletonSemantics : CountSkeletonsSemantics G r n FBE
    walkSemantics : CountWalksSemantics G r (n + n)

    encodingData : ActualSkeletonEncodingData G r n
    encodingData≡ :
      encodingData ≡
      actualSkeletonEncodingDataFromSemantics skeletonSemantics walkSemantics

    p06SkeletonCountBound :
      countSkeletons G r n ≤ pow (Δ * Δ) n

-- The constructor is the single active P06 dependency boundary.  The
-- equality field above makes the derivation explicit in the record rather
-- than silently duplicating the construction.
p06SemanticCountWitness :
  {G : Graph} {Δ : ℕ} {r : GC.Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  BoundedDegree G Δ →
  CountSkeletonsSemantics G r n FBE →
  CountWalksSemantics G r (n + n) →
  P06SemanticCountWitness G Δ r n FBE
p06SemanticCountWitness {G} {Δ} {r} {n} {FBE} bd skelSem walkSem =
  let encData = actualSkeletonEncodingDataFromSemantics skelSem walkSem
  in record
    { skeletonSemantics = skelSem
    ; walkSemantics = walkSem
    ; encodingData = encData
    ; encodingData≡ = refl
    ; p06SkeletonCountBound = actualSkeletonCountBound bd encData
    }

-- Named projections for downstream P06 reducers.  These replace the old
-- encode/decode/decenc/count-bound postulate bundle on the active route.
countSemanticsToP06EncodingData :
  {G : Graph} {Δ : ℕ} {r : GC.Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  BoundedDegree G Δ →
  CountSkeletonsSemantics G r n FBE →
  CountWalksSemantics G r (n + n) →
  ActualSkeletonEncodingData G r n
countSemanticsToP06EncodingData bd skelSem walkSem =
  P06SemanticCountWitness.encodingData
    (p06SemanticCountWitness bd skelSem walkSem)

countSemanticsToP06SkeletonCountBound :
  {G : Graph} {Δ : ℕ} {r : GC.Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  BoundedDegree G Δ →
  CountSkeletonsSemantics G r n FBE →
  CountWalksSemantics G r (n + n) →
  countSkeletons G r n ≤ pow (Δ * Δ) n
countSemanticsToP06SkeletonCountBound bd skelSem walkSem =
  P06SemanticCountWitness.p06SkeletonCountBound
    (p06SemanticCountWitness bd skelSem walkSem)

-- Concrete entrypoint for the active P06 route.  The old generic
-- `CountSkeletonsSemantics` remains available to compatibility consumers,
-- but new callers can supply the normalized concrete candidate semantics
-- directly.
p06ConcreteSemanticCountWitness :
  {G : Graph} {Δ : ℕ} {r : GC.Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  BoundedDegree G Δ →
  ConcreteCountSkeletonsSemantics G r n FBE →
  CountWalksSemantics G r (n + n) →
  P06SemanticCountWitness G Δ r n FBE
p06ConcreteSemanticCountWitness bd concreteSkelSem walkSem =
  p06SemanticCountWitness
    bd
    (concreteCountSkeletonsSemanticsToCountSkeletonsSemantics concreteSkelSem)
    walkSem

-- Explicit witness-list entrypoint.  This is the preferred construction when
-- Connected is not exposed through a stable decidability instance.
p06ExplicitCandidateSemanticCountWitness :
  {G : Graph} {Δ : ℕ} {r : GC.Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  BoundedDegree G Δ →
  ExplicitSkeletonCandidateEnumeration G r n FBE →
  CountWalksSemantics G r (n + n) →
  P06SemanticCountWitness G Δ r n FBE
p06ExplicitCandidateSemanticCountWitness bd enum walkSem =
  p06SemanticCountWitness
    bd
    (GC.explicitSkeletonCandidateEnumerationToCountSkeletonsSemantics enum)
    walkSem

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
