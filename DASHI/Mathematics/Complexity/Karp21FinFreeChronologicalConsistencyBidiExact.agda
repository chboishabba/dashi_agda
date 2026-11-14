module DASHI.Mathematics.Complexity.Karp21FinFreeChronologicalConsistencyBidiExact where

------------------------------------------------------------------------
-- N21: CHRONOLOGICAL HISTORY SCAN = ORIGINAL ALL-PAIRS CONSISTENCY.
-- On every arbitrary Nat×Bool observation list, the original
-- Runtime.endpointConsistent checker plus chronological history agrees
-- with the original Cook.allCookObservationsConsistent all-pairs scan.
-- This is not yet the whole graph verifier or a binary tape clock.
-- Source written, Agda/kernel and --safe closure NOT yet accepted.
-- Reuses Karp (1972), Cook (1971), source-owned DASHI checkers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (sym; cong; cong₂; trans)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Golden
import DASHI.Mathematics.Complexity.Karp21CookFiniteOccurrenceWitnessExact as Cook
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21FinFreeTypedObservationConsistencyBidiExact as Numeric
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21RawGraphValidatorObservationExact as Observe
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut

boolEqualSymmetric : (a b : Bool) →
  Golden.boolEqual a b ≡ Golden.boolEqual b a
boolEqualSymmetric true true = refl
boolEqualSymmetric true false = refl
boolEqualSymmetric false true = refl
boolEqualSymmetric false false = refl

cookPairCompatibleSymmetric :
  (first second : Nat × Bool) →
  Cook.compatibleCookObservations first second
    ≡ Cook.compatibleCookObservations second first
cookPairCompatibleSymmetric (u , a) (v , b)
  with NatP._≟_ u v | NatP._≟_ v u
... | yes _ | yes _ = boolEqualSymmetric a b
... | yes same | no different = ⊥-elim (different (sym same))
... | no different | yes same = ⊥-elim (different (sym same))
... | no _ | no _ = refl

-- Explicit decidable Boolean algebra; each combination has refl.
andFourSwap :
  (a b c d : Bool) →
  Golden.andBool (Golden.andBool a b) (Golden.andBool c d)
    ≡ Golden.andBool (Golden.andBool a c) (Golden.andBool b d)
andFourSwap true true true true = refl
andFourSwap true true true false = refl
andFourSwap true true false true = refl
andFourSwap true true false false = refl
andFourSwap true false true true = refl
andFourSwap true false true false = refl
andFourSwap true false false true = refl
andFourSwap true false false false = refl
andFourSwap false true true true = refl
andFourSwap false true true false = refl
andFourSwap false true false true = refl
andFourSwap false true false false = refl
andFourSwap false false true true = refl
andFourSwap false false true false = refl
andFourSwap false false false true = refl
andFourSwap false false false false = refl

andRoundSwap :
  (a b c d : Bool) →
  Golden.andBool a (Golden.andBool (Golden.andBool b c) d)
    ≡ Golden.andBool (Golden.andBool a c) (Golden.andBool b d)
andRoundSwap true true true true = refl
andRoundSwap true true true false = refl
andRoundSwap true true false true = refl
andRoundSwap true true false false = refl
andRoundSwap true false true true = refl
andRoundSwap true false true false = refl
andRoundSwap true false false true = refl
andRoundSwap true false false false = refl
andRoundSwap false true true true = refl
andRoundSwap false true true false = refl
andRoundSwap false true false true = refl
andRoundSwap false true false false = refl
andRoundSwap false false true true = refl
andRoundSwap false false true false = refl
andRoundSwap false false false true = refl
andRoundSwap false false false false = refl

crossAgainstHistory :
  List (Nat × Bool) → List (Nat × Bool) → Bool
crossAgainstHistory [] history = true
crossAgainstHistory (first ∷ rest) history =
  Golden.andBool
    (Cook.oneCookObservationAgainst first history)
    (crossAgainstHistory rest history)

crossFreshArrival :
  (entries : List (Nat × Bool))
  (arrival : Nat × Bool)
  (history : List (Nat × Bool)) →
  crossAgainstHistory entries (arrival ∷ history)
    ≡ Golden.andBool
        (Cook.oneCookObservationAgainst arrival entries)
        (crossAgainstHistory entries history)
crossFreshArrival [] arrival history = refl
crossFreshArrival (first ∷ rest) arrival history
  rewrite crossFreshArrival rest arrival history
        | cookPairCompatibleSymmetric first arrival =
  andFourSwap
    (Cook.compatibleCookObservations arrival first)
    (Cook.oneCookObservationAgainst first history)
    (Cook.oneCookObservationAgainst arrival rest)
    (crossAgainstHistory rest history)

chronologicalCookCheck :
  List (Nat × Bool) → List (Nat × Bool) → Bool
chronologicalCookCheck [] history = true
chronologicalCookCheck (first ∷ rest) history =
  Golden.andBool
    (Cook.oneCookObservationAgainst first history)
    (chronologicalCookCheck rest (first ∷ history))

chronologicalCookWithHistory :
  (entries history : List (Nat × Bool)) →
  chronologicalCookCheck entries history
    ≡ Golden.andBool
        (crossAgainstHistory entries history)
        (Cook.allCookObservationsConsistent entries)
chronologicalCookWithHistory [] history = refl
chronologicalCookWithHistory (first ∷ rest) history
  rewrite chronologicalCookWithHistory rest (first ∷ history)
        | crossFreshArrival rest first history =
  andRoundSwap
    (Cook.oneCookObservationAgainst first history)
    (Cook.oneCookObservationAgainst first rest)
    (crossAgainstHistory rest history)
    (Cook.allCookObservationsConsistent rest)

crossAgainstEmptyIsTrue :
  (entries : List (Nat × Bool)) →
  crossAgainstHistory entries [] ≡ true
crossAgainstEmptyIsTrue [] = refl
crossAgainstEmptyIsTrue (first ∷ rest)
  rewrite crossAgainstEmptyIsTrue rest = refl

chronologicalCookExactlyOriginalAllPairs :
  (entries : List (Nat × Bool)) →
  chronologicalCookCheck entries []
    ≡ Cook.allCookObservationsConsistent entries
chronologicalCookExactlyOriginalAllPairs entries =
  trans
    (chronologicalCookWithHistory entries [])
    (cong
      (λ cross →
        Golden.andBool cross
          (Cook.allCookObservationsConsistent entries))
      (crossAgainstEmptyIsTrue entries))

chronologicalRuntimeCheck :
  List (Nat × Bool) → List (Nat × Bool) → Bool
chronologicalRuntimeCheck [] history = true
chronologicalRuntimeCheck ((vertex , bit) ∷ rest) history =
  Golden.andBool
    (Runtime.endpointConsistent vertex bit history)
    (chronologicalRuntimeCheck rest ((vertex , bit) ∷ history))

chronologicalRuntimeIsCook :
  (entries history : List (Nat × Bool)) →
  chronologicalRuntimeCheck entries history
    ≡ chronologicalCookCheck entries history
chronologicalRuntimeIsCook [] history = refl
chronologicalRuntimeIsCook ((vertex , bit) ∷ rest) history =
  cong₂ Golden.andBool
    (Numeric.runtimeHistoryCheckExactlyCook vertex bit history)
    (chronologicalRuntimeIsCook
      rest ((vertex , bit) ∷ history))

-- Crucial schedule-independent result using original Runtime primitive
-- and the exact original Cook all-pairs predicate.
chronologicalRuntimeExactlyOriginalAllPairs :
  (entries : List (Nat × Bool)) →
  chronologicalRuntimeCheck entries []
    ≡ Cook.allCookObservationsConsistent entries
chronologicalRuntimeExactlyOriginalAllPairs entries =
  trans
    (chronologicalRuntimeIsCook entries [])
    (chronologicalCookExactlyOriginalAllPairs entries)

------------------------------------------------------------------------
-- Apply the generic chronological theorem to EXACT TWO endpoints
-- per original signed raw edge. The raw history after each edge
-- is (u,a)::(v,b)::history, exactly the original rawSparseScore
-- implementation. Reverse only the visitation within each edge.
------------------------------------------------------------------------

reverseOriginalRawEndpointPairs :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n)) →
  Observe.RawEdgeListFieldsSame raw typed →
  Sparse.EdgeBits typed → List (Nat × Bool)
reverseOriginalRawEndpointPairs [] []
  Observe.raw-list-nil Sparse.emptyEdgeBits = []
reverseOriginalRawEndpointPairs
  (r ∷ rs) (edge ∷ es)
  (Observe.raw-list-cons fields restFields)
  (Sparse.addEdgeBits a b restBits) =
  (Graph.target r , b) ∷ (Graph.source r , a)
    ∷ reverseOriginalRawEndpointPairs rs es restFields restBits

rawOriginalRuntimeHistoryGuard :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n)) →
  Observe.RawEdgeListFieldsSame raw typed →
  Sparse.EdgeBits typed →
  List (Nat × Bool) → Bool
rawOriginalRuntimeHistoryGuard [] []
  Observe.raw-list-nil Sparse.emptyEdgeBits history = true
rawOriginalRuntimeHistoryGuard
  (r ∷ rs) (edge ∷ es)
  (Observe.raw-list-cons fields restFields)
  (Sparse.addEdgeBits a b restBits) history =
  Golden.andBool
    (Runtime.endpointConsistent (Graph.source r) a history)
    (Golden.andBool
      (Runtime.endpointConsistent (Graph.target r) b history)
      (rawOriginalRuntimeHistoryGuard
        rs es restFields restBits
        ((Graph.source r , a) ∷ (Graph.target r , b) ∷ history)))

-- Same acceptance Bool using the actual Runtime two endpoint checks,
-- even though the ordinary chronological checker visits v then u.
rawOriginalRuntimeHistoryEqualsChronological :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n))
    (fields : Observe.RawEdgeListFieldsSame raw typed)
    (bits : Sparse.EdgeBits typed)
    (history : List (Nat × Bool)) →
  rawOriginalRuntimeHistoryGuard raw typed fields bits history
    ≡ chronologicalRuntimeCheck
        (reverseOriginalRawEndpointPairs raw typed fields bits)
        history
rawOriginalRuntimeHistoryEqualsChronological [] []
  Observe.raw-list-nil Sparse.emptyEdgeBits history = refl
rawOriginalRuntimeHistoryEqualsChronological
  (r ∷ rs) (edge ∷ es)
  (Observe.raw-list-cons fields restFields)
  (Sparse.addEdgeBits a b restBits) history
  rewrite rawOriginalRuntimeHistoryEqualsChronological
    rs es restFields restBits
    ((Graph.source r , a) ∷ (Graph.target r , b) ∷ history) =
  Numeric.rawPairOldHistoryEqualsSequentialChronology
    r edge fields a b
    (chronologicalRuntimeCheck
      (reverseOriginalRawEndpointPairs rs es restFields restBits)
      ((Graph.source r , a) ∷ (Graph.target r , b) ∷ history))
    history

rawOriginalRuntimeHistoryExactlyCookAllPairs :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n))
    (fields : Observe.RawEdgeListFieldsSame raw typed)
    (bits : Sparse.EdgeBits typed) →
  rawOriginalRuntimeHistoryGuard raw typed fields bits []
    ≡ Cook.allCookObservationsConsistent
        (reverseOriginalRawEndpointPairs raw typed fields bits)
rawOriginalRuntimeHistoryExactlyCookAllPairs raw typed fields bits =
  trans
    (rawOriginalRuntimeHistoryEqualsChronological
      raw typed fields bits [])
    (chronologicalRuntimeExactlyOriginalAllPairs
      (reverseOriginalRawEndpointPairs raw typed fields bits))
