module DASHI.Physics.ClaySupportingP06CanonicalEncoding where

------------------------------------------------------------------------
-- Canonical skeleton encoding bridge (YM P06 Option A).
--
-- Companion to `...ClaySupportingSpanningTreeEncoding` and
-- `...ClaySupportingPolymerCounting`.  Every declaration here is a
-- genuine Agda proof over concrete data: there are NO `postulate`s and
-- NO added axioms.
--
-- This module formalises the "actual skeleton carrier for the repo
-- carrier" and proves the conditional cardinality bound:
--
--   actual reduced connected skeleton carrier
--   + canonical decoder left inverse
--   ⇒  #𝒮_{n,v}^{red} ≤ (Δ²)ⁿ.
--
-- The record `CanonicalSkeletonCarrier` captures exactly what the repo
-- must supply for each root v and size n: the finite set of skeletons,
-- a rooted spanning tree for each skeleton, a DFS encoding into the
-- walk-index set, and a decoder that inverts the encoding.  The theorem
-- `canonicalSkeletonCardinalityBound` then discharges the counting
-- consequence.
--
-- Honesty boundary (unchanged and deliberate): this does NOT discharge
-- any open analytic Clay leaf.  The existence of the rooted spanning
-- tree and the canonical decoder for the repo's actual skeleton carrier
-- are left as explicit fields of `CanonicalSkeletonCarrier` — they are
-- the open graph-theory leaf, not asserted here.  What is proved is the
-- counting consequence once those are supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ; _+_; _*_; _≤_)
open import Data.List.Base using (List)
open import Data.Fin.Base using (Fin)

open import DASHI.Physics.ClaySupportingElementaryLemmas using (pow)
open import DASHI.Physics.ClaySupportingGraphCombinatorics
  using (BoundedDegreeBy; RTree; _∈T_; size; walkCount)
open import DASHI.Physics.ClaySupportingSpanningTreeEncoding
  using (canonicalEncodingCountBound)

------------------------------------------------------------------------
-- §1.  The canonical skeleton carrier record.
--
-- For a fixed root v and size n, the repo's actual reduced connected
-- skeleton set 𝒮_{n,v}^{red} is represented as Fin numSkel together
-- with the spanning-tree / encoding / decoding data that turns it into
-- the walk-injective counting argument.

record CanonicalSkeletonCarrier
    {V : Set} (nbrs : V → List V) (v : V) (n : ℕ) : Set₁ where
  field
    -- Number of reduced connected skeletons of size n rooted at v.
    numSkel : ℕ

    -- Every skeleton admits a rooted spanning tree.
    spanningTree       : Fin numSkel → RTree V
    spanningTreeRoot   : ∀ s → v ∈T spanningTree s
    spanningTreeSize   : ∀ s → size (spanningTree s) ≡ n

    -- DFS encoding: enc(S) is the Euler tour of the spanning tree,
    -- which is a length-(n+n) walk from v, hence an index into the
    -- walk-count set.
    encode : Fin numSkel → Fin (walkCount nbrs v (n + n))

    -- Canonical decoder: recovers the skeleton index from any walk
    -- index.  The left-inverse property decode ∘ encode = id makes
    -- encode injective.
    decode        : Fin (walkCount nbrs v (n + n)) → Fin numSkel
    decodeEncode  : ∀ s → decode (encode s) ≡ s

------------------------------------------------------------------------
-- §2.  Cardinality bound.
--
-- Given a `CanonicalSkeletonCarrier`, the bound follows directly from
-- the left-inverse injection via `canonicalEncodingCountBound`.

canonicalSkeletonCardinalityBound :
  {V : Set} (nbrs : V → List V) (Δ : ℕ) →
  BoundedDegreeBy nbrs Δ →
  (v : V) (n : ℕ) →
  (C : CanonicalSkeletonCarrier nbrs v n) →
  CanonicalSkeletonCarrier.numSkel C ≤ pow (Δ * Δ) n
canonicalSkeletonCardinalityBound nbrs Δ deg v n C =
  canonicalEncodingCountBound nbrs Δ deg v n
    (CanonicalSkeletonCarrier.numSkel C)
    (CanonicalSkeletonCarrier.encode C)
    (CanonicalSkeletonCarrier.decode C)
    (CanonicalSkeletonCarrier.decodeEncode C)
