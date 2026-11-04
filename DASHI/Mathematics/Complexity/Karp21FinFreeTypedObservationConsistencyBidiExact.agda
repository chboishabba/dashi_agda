module DASHI.Mathematics.Complexity.Karp21FinFreeTypedObservationConsistencyBidiExact where

------------------------------------------------------------------------
-- N21: SAME ORIGINAL SPARSE CERTIFICATE ENDPOINT OBSERVATIONS.
--
-- Existing Sparse.allEndpointOccurrencesConsistent uses Fin equality,
-- whereas existing Finite.allCookObservationsConsistent uses Nat
-- equality and Runtime.endpointConsistent scans a Nat history.
-- FinP.toℕ-injective connects BOTH original comparison routines,
-- for all n and all signed graph edges, with no bounded-n assumption.
--
-- This also transports the ORIGINAL raw signed weights, not only a
-- Boolean acceptance flag. The raw observation list and local edge
-- score below are mathematical comparison carriers, NOT substitute
-- runtime checkers. The history order, nested parser, complete score
-- decision and true binary tape clock remain outstanding.
--
-- All source-written, Agda kernel / --safe import closure unverified.
-- Original algorithm: Karp (1972). Proof reuse: DASHI Cook pairwise
-- observation checker and the existing sparse MaxCut/Fin-free owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (sym; cong; cong₂)
import Data.Nat.Properties as NatP
import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP
import Data.Integer.Base as Int

import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Golden
import DASHI.Mathematics.Complexity.Karp21CookFiniteOccurrenceWitnessExact as Finite
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21RawGraphValidatorObservationExact as Observe
import DASHI.Mathematics.Complexity.Karp21FinFreeAllRawValidatorAgreementExact as AllRaw

-- Erase ONLY the representation of the actual Fin vertex address.
-- The Boolean value and original occurrence order remain unchanged.
numericEndpointObservation :
  ∀ {n : Nat} → (Fin.Fin n × Bool) → Nat × Bool
numericEndpointObservation (vertex , bit) = Fin.toℕ vertex , bit

numericEndpointObservations :
  ∀ {n : Nat} → List (Fin.Fin n × Bool) → List (Nat × Bool)
numericEndpointObservations [] = []
numericEndpointObservations (first ∷ rest) =
  numericEndpointObservation first ∷ numericEndpointObservations rest

-- Fin equality iff numeric address equality. Comparing signed weights
-- or enumerating all n possible vertices is unnecessary.
typedNumericPairCompatible :
  ∀ {n : Nat}
    (first second : Fin.Fin n × Bool) →
  Sparse.observationsCompatible first second
    ≡ Finite.compatibleCookObservations
        (numericEndpointObservation first)
        (numericEndpointObservation second)
typedNumericPairCompatible (v , a) (w , b)
  with FinP._≟_ v w | NatP._≟_ (Fin.toℕ v) (Fin.toℕ w)
... | yes _ | yes _ = refl
... | yes equal | no different =
  ⊥-elim (different (cong Fin.toℕ equal))
... | no different | yes equal =
  ⊥-elim (different (FinP.toℕ-injective equal))
... | no _ | no _ = refl

-- Same EXACT all-pairs primitive on the same typed endpoint list.
typedOneAgainstNumericCook :
  ∀ {n : Nat}
    (first : Fin.Fin n × Bool)
    (rest : List (Fin.Fin n × Bool)) →
  Sparse.oneAgainstAll first rest
    ≡ Finite.oneCookObservationAgainst
        (numericEndpointObservation first)
        (numericEndpointObservations rest)
typedOneAgainstNumericCook first [] = refl
typedOneAgainstNumericCook first (other ∷ rest) =
  cong₂ Golden.andBool
    (typedNumericPairCompatible first other)
    (typedOneAgainstNumericCook first rest)

typedAllPairsExactlyNumericCook :
  ∀ {n : Nat} (entries : List (Fin.Fin n × Bool)) →
  Sparse.allEndpointOccurrencesConsistent entries
    ≡ Finite.allCookObservationsConsistent
        (numericEndpointObservations entries)
typedAllPairsExactlyNumericCook [] = refl
typedAllPairsExactlyNumericCook (first ∷ rest) =
  cong₂ Golden.andBool
    (typedOneAgainstNumericCook first rest)
    (typedAllPairsExactlyNumericCook rest)

-- The ACTUAL original Fin-free history checker is precisely the
-- Cook-source all-pairs one-versus-list primitive, pointwise.
runtimeHistoryCheckExactlyCook :
  (vertex : Nat) (selected : Bool)
  (history : List (Nat × Bool)) →
  Runtime.endpointConsistent vertex selected history
    ≡ Finite.oneCookObservationAgainst
        (vertex , selected) history
runtimeHistoryCheckExactlyCook vertex selected [] = refl
runtimeHistoryCheckExactlyCook
  vertex selected ((other , observed) ∷ rest)
  with NatP._≟_ vertex other
... | yes _ =
  cong (Golden.andBool (Golden.boolEqual selected observed))
    (runtimeHistoryCheckExactlyCook vertex selected rest)
... | no _ = runtimeHistoryCheckExactlyCook vertex selected rest

------------------------------------------------------------------------
-- The existing dependent raw parser already certifies each endpoint
-- address and signed weight against the same raw edge triple. Apply
-- those certificates to the original EXACT 2m-bit EdgeBits carrier.
------------------------------------------------------------------------

originalRawEndpointPairs :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n)) →
  Observe.RawEdgeListFieldsSame raw typed →
  Sparse.EdgeBits typed →
  List (Nat × Bool)
originalRawEndpointPairs [] [] Observe.raw-list-nil
  Sparse.emptyEdgeBits = []
originalRawEndpointPairs
  (r ∷ rs) (edge ∷ es)
  (Observe.raw-list-cons fields restFields)
  (Sparse.addEdgeBits a b restBits) =
  (Graph.source r , a) ∷ (Graph.target r , b)
    ∷ originalRawEndpointPairs rs es restFields restBits

originalRawPairsAreTypedNumericPairs :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n))
    (fields : Observe.RawEdgeListFieldsSame raw typed)
    (bits : Sparse.EdgeBits typed) →
  originalRawEndpointPairs raw typed fields bits
    ≡ numericEndpointObservations
        (Sparse.endpointObservations typed bits)
originalRawPairsAreTypedNumericPairs [] [] Observe.raw-list-nil
  Sparse.emptyEdgeBits = refl
originalRawPairsAreTypedNumericPairs
  (r ∷ rs) (edge ∷ es)
  (Observe.raw-list-cons same restSame)
  (Sparse.addEdgeBits a b restBits)
  rewrite sym (Observe.firstAddress same)
        | sym (Observe.secondAddress same)
        | originalRawPairsAreTypedNumericPairs
            rs es restSame restBits = refl

-- This is EXACT same-original-bitword local-certificate consistency:
-- each occurrence is labelled by its input certificate bit in order.
originalRawPairsTypedConsistencySame :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n))
    (fields : Observe.RawEdgeListFieldsSame raw typed)
    (bits : Sparse.EdgeBits typed) →
  Finite.allCookObservationsConsistent
    (originalRawEndpointPairs raw typed fields bits)
    ≡ Sparse.allEndpointOccurrencesConsistent
        (Sparse.endpointObservations typed bits)
originalRawPairsTypedConsistencySame raw typed fields bits
  rewrite originalRawPairsAreTypedNumericPairs
    raw typed fields bits =
  sym (typedAllPairsExactlyNumericCook
    (Sparse.endpointObservations typed bits))

------------------------------------------------------------------------
-- Original signed MAX CUT objective. This local fold projects raw
-- triples and original bits without replacing the runtime score code.
-- Every edge uses the source-owned raw signedWeight, including <0.
------------------------------------------------------------------------

originalRawLocalSignedCut :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n)) →
  Observe.RawEdgeListFieldsSame raw typed →
  Sparse.EdgeBits typed → Int.ℤ
originalRawLocalSignedCut [] [] Observe.raw-list-nil
  Sparse.emptyEdgeBits = Int.+ 0
originalRawLocalSignedCut
  (r ∷ rs) (edge ∷ es)
  (Observe.raw-list-cons fields restFields)
  (Sparse.addEdgeBits a b restBits) =
  Int._+_
    (AllRaw.rawEdgeContribution (Graph.signedWeight r) a b)
    (originalRawLocalSignedCut rs es restFields restBits)

originalRawLocalSignedCutMatchesTyped :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n))
    (fields : Observe.RawEdgeListFieldsSame raw typed)
    (bits : Sparse.EdgeBits typed) →
  originalRawLocalSignedCut raw typed fields bits
    ≡ Sparse.sparseEdgeScore typed bits
originalRawLocalSignedCutMatchesTyped [] [] Observe.raw-list-nil
  Sparse.emptyEdgeBits = refl
originalRawLocalSignedCutMatchesTyped
  (r ∷ rs) (edge ∷ es)
  (Observe.raw-list-cons same restSame)
  (Sparse.addEdgeBits a b restBits) =
  cong₂ Int._+_
    (AllRaw.sameRawSignedCrossingContribution r edge same a b)
    (originalRawLocalSignedCutMatchesTyped
      rs es restSame restBits)

