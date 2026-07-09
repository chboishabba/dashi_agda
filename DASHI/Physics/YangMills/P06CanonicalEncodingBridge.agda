module DASHI.Physics.YangMills.P06CanonicalEncodingBridge where

------------------------------------------------------------------------
-- Adapter that instantiates the `CanonicalSkeletonCarrier` interface
-- (from `ClaySupportingP06CanonicalEncoding`) for the repo's actual P06
-- graph model, then derives the exponential size-shell counting bound
-- `numSkel ≤ (Δ²)ⁿ` via `canonicalSkeletonCardinalityBound`.
--
-- Structure:
--   Layer 1 — Graph model  (postulated):
--     V (vertices), nbrs (concrete adjacency), Δ (degree bound),
--     bounded-degree proof.
--   Layer 2 — Skeleton carrier  (postulated):
--     The skeleton size-shell counts, encode, decode, decodeEncode,
--     and rooted spanning tree.
--   Layer 3 — Canonical carrier + counting bound  (proved):
--     `currentP06CanonicalCardinalityBound`.
--   Layer 4 — ProofTargetSurface  (proved):
--     Documents the conditional theorem.
--
-- Honesty: Layers 1 and 2 are open.  No analytic Clay leaf is
-- discharged by this bridge; what is proved is that once those
-- postulates are inhabited, the exponential bound follows.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; _*_; _+_; _≤_)
open import Data.List.Base using (List; length)
open import Data.String using (_++_)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.ClaySupportingElementaryLemmas using (pow)
open import DASHI.Physics.ClaySupportingGraphCombinatorics
  using (BoundedDegreeBy; walkCount; RTree; _∈T_; size)
open import DASHI.Physics.ClaySupportingP06CanonicalEncoding
  using (CanonicalSkeletonCarrier; canonicalSkeletonCardinalityBound)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using (Graph; BoundedDegree; countNeighbors)
open import DASHI.Physics.YangMills.ProofTargetSurface
  using (ProofTargetSurface; mkProofTargetSurfaceWithAuthority; ProofStatus)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface
  using (dashi-internal-proof; proved; consequence-proof)

------------------------------------------------------------------------
-- Layer 1 — Graph model
------------------------------------------------------------------------

-- The repo's vertex set and concrete adjacency are postulated.
postulate
  V : Set
  nbrs : V → List V
  Δ : ℕ

  -- The repo's BoundedDegree proof provides an upper bound on neighbor
  -- counts.  We postulate a concrete neighbour-list translation.
  repoBoundedDegree : BoundedDegreeBy nbrs Δ

nbrs-bounded-degree : BoundedDegreeBy nbrs Δ
nbrs-bounded-degree = repoBoundedDegree

------------------------------------------------------------------------
-- Layer 2 — Skeleton carrier (open leaf)
------------------------------------------------------------------------

-- Postulated size-shell skeleton count (the repo's P06 count).
postulate
  sizeShellCountAt : V → ℕ → ℕ

  currentP06Encode :
    (v : V) (n : ℕ) →
    Fin (sizeShellCountAt v n) →
    Fin (walkCount nbrs v (n + n))

  currentP06Decode :
    (v : V) (n : ℕ) →
    Fin (walkCount nbrs v (n + n)) →
    Fin (sizeShellCountAt v n)

  currentP06DecodeEncode :
    (v : V) (n : ℕ)
    (s : Fin (sizeShellCountAt v n)) →
    currentP06Decode v n (currentP06Encode v n s) ≡ s

  currentP06SpanningTree :
    (v : V) (n : ℕ) →
    Fin (sizeShellCountAt v n) →
    RTree V

  currentP06SpanningTreeRoot :
    (v : V) (n : ℕ)
    (s : Fin (sizeShellCountAt v n)) →
    v ∈T currentP06SpanningTree v n s

  currentP06SpanningTreeSize :
    (v : V) (n : ℕ)
    (s : Fin (sizeShellCountAt v n)) →
    size (currentP06SpanningTree v n s) ≡ n

------------------------------------------------------------------------
-- Layer 3 — Canonical skeleton carrier + counting bound
------------------------------------------------------------------------

currentP06CanonicalSkeletonCarrier :
  (v : V) (n : ℕ) →
  CanonicalSkeletonCarrier nbrs v n
currentP06CanonicalSkeletonCarrier v n = record
  { numSkel = sizeShellCountAt v n
  ; spanningTree = currentP06SpanningTree v n
  ; spanningTreeRoot = currentP06SpanningTreeRoot v n
  ; spanningTreeSize = currentP06SpanningTreeSize v n
  ; encode = currentP06Encode v n
  ; decode = currentP06Decode v n
  ; decodeEncode = currentP06DecodeEncode v n
  }

currentP06CanonicalCardinalityBound :
  (v : V) (n : ℕ) →
  sizeShellCountAt v n ≤ pow (Δ * Δ) n
currentP06CanonicalCardinalityBound v n =
  canonicalSkeletonCardinalityBound nbrs Δ nbrs-bounded-degree v n
    (currentP06CanonicalSkeletonCarrier v n)

------------------------------------------------------------------------
-- Layer 4 — ProofTargetSurface  (conditional theorem documentation)

currentP06CanonicalCardinalitySurface : ProofTargetSurface
currentP06CanonicalCardinalitySurface =
  mkProofTargetSurfaceWithAuthority
    "P06CanonicalCardinalityBound"
    "DASHI canonical encoding bridge (P06 internal)"
    ("#𝒮_{n,v}^{red} ≤ (Δ²)ⁿ — derived from CanonicalSkeletonCarrier "
     ++ "via canonicalSkeletonCardinalityBound, conditional on "
     ++ "encode/decode/decodeEncode postulates (open graph-theory leaf).")
    ("CanonicalSkeletonCarrier instantiated for abstract nbrs, V, Δ; "
     ++ "all input postulates are open.")
    ("#𝒮_{n,v}^{red} ≤ (Δ²)ⁿ")
    "currentP06CanonicalCardinalityBound"
    "P06 counting"
    proved
    dashi-internal-proof
    "P06CanonicalEncodingBridge.currentP06CanonicalCardinalityBound"
    consequence-proof
    proved
