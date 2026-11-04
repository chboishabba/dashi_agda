module DASHI.Mathematics.Complexity.Karp21FinFreeActualSparseScoreAcceptanceExact where

------------------------------------------------------------------------
-- N21: ACTUAL Runtime.rawSparseScore MAYBE RESULT IS THE SAME
-- SIGNED 2m-BIT SPARSE CUT SCORE AS THE ORIGINAL TYPED VERIFIER.
--
-- The actual rawSparseScore rejects inconsistent endpoint labels and
-- wrong bit length with nothing; on accepted EXACT EdgeBits encoding,
-- its signed result must be the original Sparse.sparseEdgeScore.
-- Reuse the existing raw-history ↔ typed pairwise bridge and the
-- source-owned raw-to-typed signed edge observation/score lemma.
-- No >0/PSD weight assumption: negative ℤ edge contributions retained.
--
-- Here the typed EdgeBits is supplied by the same original decoded
-- graph; a future N21 theorem must cover arbitrary bitwords, malformed
-- graph words and the outer positive-threshold comparison. Executable
-- polynomial binary Turing-tape time and Agda kernel receipt OPEN.
--
-- Karp 1972; DASHI original signed N21/Cook/Fin-free proof owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
import Data.Integer.Base as Int
import Data.Integer.Properties as IntP

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Golden
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21RawGraphValidatorObservationExact as Observe
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21FinFreeTypedObservationConsistencyBidiExact as Numeric
import DASHI.Mathematics.Complexity.Karp21FinFreeChronologicalConsistencyBidiExact as Chron
import DASHI.Mathematics.Complexity.Karp21FinFreeActualPairwiseConsistencySameExact as Pairs

-- A concrete data-constructor chooser; never a resource oracle.
scoreWhenHistoryAccepts : Bool → Int.ℤ → Maybe Int.ℤ
scoreWhenHistoryAccepts true value = just value
scoreWhenHistoryAccepts false value = nothing

-- The literal source Runtime.rawSparseScore either rejects according
-- to the actual original endpointConsistent history schedule, or
-- returns the entire original signed raw-local contribution fold.
rawSparseScoreExactlyExpected :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n))
    (fields : Observe.RawEdgeListFieldsSame raw typed)
    (bits : Sparse.EdgeBits typed)
    (history : List (Nat × Bool)) →
  Runtime.rawSparseScore raw (Sparse.encodeSparseEdgeBits bits) history
    ≡ scoreWhenHistoryAccepts
        (Chron.rawOriginalRuntimeHistoryGuard
          raw typed fields bits history)
        (Numeric.originalRawLocalSignedCut raw typed fields bits)
rawSparseScoreExactlyExpected [] [] Observe.raw-list-nil
  Sparse.emptyEdgeBits history = refl
rawSparseScoreExactlyExpected
  (r ∷ rs) (edge ∷ es)
  (Observe.raw-list-cons fields tailFields)
  (Sparse.addEdgeBits a b tailBits) history
  with Runtime.endpointConsistent (Graph.source r) a history
     | Runtime.endpointConsistent (Graph.target r) b history
... | false | _ = refl
... | true | false = refl
... | true | true
  rewrite rawSparseScoreExactlyExpected
    rs es tailFields tailBits
    ((Graph.source r , a) ∷ (Graph.target r , b) ∷ history)
  with Chron.rawOriginalRuntimeHistoryGuard
    rs es tailFields tailBits
    ((Graph.source r , a) ∷ (Graph.target r , b) ∷ history)
...   | false = refl
...   | true with Golden.boolEqual a b
...     | true =
  cong just
    (sym (IntP.+-identityˡ
      (Numeric.originalRawLocalSignedCut
        rs es tailFields tailBits)))
...     | false = refl

scoreWhenHistoryAcceptedExactly :
  (ok : Bool) (score : Int.ℤ) →
  scoreWhenHistoryAccepts ok score ≡ just score →
  ok ≡ true
scoreWhenHistoryAcceptedExactly true score accepted = refl
scoreWhenHistoryAcceptedExactly false score ()

rawScoreAcceptedIffHistoryConsistent :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n))
    (fields : Observe.RawEdgeListFieldsSame raw typed)
    (bits : Sparse.EdgeBits typed)
    (history : List (Nat × Bool)) →
  PR.Iff
    (Runtime.rawSparseScore raw
      (Sparse.encodeSparseEdgeBits bits) history
      ≡ just (Numeric.originalRawLocalSignedCut
        raw typed fields bits))
    (Chron.rawOriginalRuntimeHistoryGuard
      raw typed fields bits history ≡ true)
rawScoreAcceptedIffHistoryConsistent raw typed fields bits history =
  let score = Numeric.originalRawLocalSignedCut raw typed fields bits
      check = Chron.rawOriginalRuntimeHistoryGuard
        raw typed fields bits history
      exact = rawSparseScoreExactlyExpected
        raw typed fields bits history
  in PR.iff
       (λ accepted →
         scoreWhenHistoryAcceptedExactly check score
           (trans (sym exact) accepted))
       (λ guardTrue →
         trans exact
           (cong (λ value → scoreWhenHistoryAccepts value score)
             guardTrue))

------------------------------------------------------------------------
-- SAME ORIGINAL TWO-BITS-PER-EDGE WITNESS: accepted original Runtime
-- signed score iff original typed sparse endpoint consistency passes.
-- Both displayed scores use the original Sparse.sparseEdgeScore.
------------------------------------------------------------------------

rawScoreSameTypedSparseConsistencyIff :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n))
    (fields : Observe.RawEdgeListFieldsSame raw typed)
    (bits : Sparse.EdgeBits typed) →
  PR.Iff
    (Runtime.rawSparseScore raw
      (Sparse.encodeSparseEdgeBits bits) []
      ≡ just (Sparse.sparseEdgeScore typed bits))
    (Sparse.allEndpointOccurrencesConsistent
      (Sparse.endpointObservations typed bits) ≡ true)
rawScoreSameTypedSparseConsistencyIff raw typed fields bits =
  let scoreSame =
        Numeric.originalRawLocalSignedCutMatchesTyped
          raw typed fields bits
      historySame =
        Pairs.rawHistorySameOriginalTypedSparseConsistency
          raw typed fields bits
      scoreIff =
        rawScoreAcceptedIffHistoryConsistent
          raw typed fields bits []
  in PR.iff
       (λ accepted →
         trans (sym historySame)
           (PR.forward scoreIff
             (trans accepted (sym (cong just scoreSame)))))
       (λ accepted →
         trans
           (PR.backward scoreIff
             (trans historySame accepted))
           (cong just scoreSame))
