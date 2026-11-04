module DASHI.Mathematics.Complexity.Karp21FinFreeActualPairwiseConsistencySameExact where

------------------------------------------------------------------------
-- N21: ACTUAL RAW HISTORY CONSISTENCY = ORIGINAL TYPED SPARSE CHECK.
--
-- The existing raw verifier inserts each edge's endpoint observations
-- in (u,a),(v,b) history order, while the chronological lemma visits
-- the pair as (v,b),(u,a). Symmetric original Cook compatibility makes
-- the complete all-pairs check invariant under EVERY within-edge swap.
-- No witness length n, finite-graph image restriction or new codec.
--
-- The exact source-owned RawEdgeListFieldsSame relation guarantees
-- the raw and typed edges refer to the SAME numeric endpoints/weights.
-- This is consistency only; signed rawSparseScore/Maybe branches,
-- arbitrary whole-word decoder, binary tape clock, Agda kernel pending.
--
-- Reuse: Karp 1972, Cook 1971, DASHI source Golden/Fin/Raw owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Golden
import DASHI.Mathematics.Complexity.Karp21CookFiniteOccurrenceWitnessExact as Cook
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21RawGraphValidatorObservationExact as Observe
import DASHI.Mathematics.Complexity.Karp21FinFreeTypedObservationConsistencyBidiExact as Numeric
import DASHI.Mathematics.Complexity.Karp21FinFreeChronologicalConsistencyBidiExact as Chron

-- Any pair of consecutive observation entries may exchange places:
-- all equality comparisons are symmetric and Boolean AND reorders.
allCookSwapHead :
  (first second : Nat × Bool)
  (rest : List (Nat × Bool)) →
  Cook.allCookObservationsConsistent (first ∷ second ∷ rest)
    ≡ Cook.allCookObservationsConsistent (second ∷ first ∷ rest)
allCookSwapHead first second rest
  rewrite Chron.cookPairCompatibleSymmetric first second =
  Chron.andFourSwap
    (Cook.compatibleCookObservations second first)
    (Cook.oneCookObservationAgainst first rest)
    (Cook.oneCookObservationAgainst second rest)
    (Cook.allCookObservationsConsistent rest)

-- A common two-element prefix remains consistent with a suffix
-- replacement iff every earlier-vs-suffix comparison is transported.
allCookTwoPrefixTailTransport :
  (first second : Nat × Bool)
  (old new : List (Nat × Bool)) →
  (∀ point →
    Cook.oneCookObservationAgainst point old
      ≡ Cook.oneCookObservationAgainst point new) →
  Cook.allCookObservationsConsistent old
    ≡ Cook.allCookObservationsConsistent new →
  Cook.allCookObservationsConsistent (first ∷ second ∷ old)
    ≡ Cook.allCookObservationsConsistent (first ∷ second ∷ new)
allCookTwoPrefixTailTransport first second old new crossEq allEq
  rewrite crossEq first | crossEq second | allEq = refl

-- Swapping every within-edge pair preserves comparisons against
-- an arbitrary checkpoint observation, including equal-index conflicts.
rawOneAgainstSwapAllEdges :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n))
    (fields : Observe.RawEdgeListFieldsSame raw typed)
    (bits : Sparse.EdgeBits typed)
    (point : Nat × Bool) →
  Cook.oneCookObservationAgainst point
    (Numeric.originalRawEndpointPairs raw typed fields bits)
    ≡ Cook.oneCookObservationAgainst point
        (Chron.reverseOriginalRawEndpointPairs raw typed fields bits)
rawOneAgainstSwapAllEdges [] [] Observe.raw-list-nil
  Sparse.emptyEdgeBits point = refl
rawOneAgainstSwapAllEdges
  (r ∷ rs) (edge ∷ es)
  (Observe.raw-list-cons same restSame)
  (Sparse.addEdgeBits a b restBits) point
  rewrite rawOneAgainstSwapAllEdges
    rs es restSame restBits point =
  Numeric.andSwap3
    (Cook.compatibleCookObservations
      point (Graph.source r , a))
    (Cook.compatibleCookObservations
      point (Graph.target r , b))
    (Cook.oneCookObservationAgainst point
      (Chron.reverseOriginalRawEndpointPairs rs es restSame restBits))

-- Whole-list invariant, not merely one-edge commutativity. This
-- carries exactly the same signed graph and 2m-bit certificate.
rawAllPairsWithinEdgeSwapInvariant :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n))
    (fields : Observe.RawEdgeListFieldsSame raw typed)
    (bits : Sparse.EdgeBits typed) →
  Cook.allCookObservationsConsistent
    (Numeric.originalRawEndpointPairs raw typed fields bits)
    ≡ Cook.allCookObservationsConsistent
        (Chron.reverseOriginalRawEndpointPairs raw typed fields bits)
rawAllPairsWithinEdgeSwapInvariant [] []
  Observe.raw-list-nil Sparse.emptyEdgeBits = refl
rawAllPairsWithinEdgeSwapInvariant
  (r ∷ rs) (edge ∷ es)
  (Observe.raw-list-cons same restSame)
  (Sparse.addEdgeBits a b restBits) =
  trans
    (allCookTwoPrefixTailTransport
      (Graph.source r , a) (Graph.target r , b)
      (Numeric.originalRawEndpointPairs rs es restSame restBits)
      (Chron.reverseOriginalRawEndpointPairs rs es restSame restBits)
      (rawOneAgainstSwapAllEdges rs es restSame restBits)
      (rawAllPairsWithinEdgeSwapInvariant rs es restSame restBits))
    (allCookSwapHead
      (Graph.source r , a) (Graph.target r , b)
      (Chron.reverseOriginalRawEndpointPairs rs es restSame restBits))

------------------------------------------------------------------------
-- Terminal N21 *CONSISTENCY* bridge on the original same 2m bits:
--
--  original raw endpointConsistent history schedule
--   = chronological Runtime check on reversed edge pairs
--   = original Cook all-pairs on reversed edge pairs
--   = original Cook all-pairs on source-order edge pairs
--   = original Sparse all-pairs on typed Fin edge occurrences.
--
-- No threshold or numeric score is used to establish this equality.
------------------------------------------------------------------------

rawHistorySameOriginalTypedSparseConsistency :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n))
    (fields : Observe.RawEdgeListFieldsSame raw typed)
    (bits : Sparse.EdgeBits typed) →
  Chron.rawOriginalRuntimeHistoryGuard raw typed fields bits []
    ≡ Sparse.allEndpointOccurrencesConsistent
        (Sparse.endpointObservations typed bits)
rawHistorySameOriginalTypedSparseConsistency raw typed fields bits =
  trans
    (Chron.rawOriginalRuntimeHistoryExactlyCookAllPairs
      raw typed fields bits)
    (trans
      (sym (rawAllPairsWithinEdgeSwapInvariant raw typed fields bits))
      (Numeric.originalRawPairsTypedConsistencySame
        raw typed fields bits))
