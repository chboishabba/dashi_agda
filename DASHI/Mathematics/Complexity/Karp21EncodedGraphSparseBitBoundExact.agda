module DASHI.Mathematics.Complexity.Karp21EncodedGraphSparseBitBoundExact where

------------------------------------------------------------------------
-- N21 / E20: ACTUAL GRAPH-WORD SPARSE CERTIFICATE SIZE RECEIPT.
--
-- On the original weighted graph and the literal gamma/zigzag wire
-- encoder, every listed edge produces at least TWO endpoint gamma bits.
-- Therefore the existing sparse witness of exactly 2m bits cannot
-- exceed the length of the encoded graph itself.
--
-- This proves a property of the REAL encoder, without replacing the
-- Karp graph or declaring a false n <= input-length bound. In
-- particular, n may be exponentially larger than the word length:
-- only the listed m edge occurrences determine witness length.
--
-- The theorem does NOT prove decoder(encoder(G)) = G for arbitrary
-- graphs (duplicate/out-of-order edge lists are correctly rejected),
-- nor a polynomial bit-machine clock for the parser or verifier.
--
-- Attribution: Karp (1972) weighted MAX CUT; DASHI original gamma
-- signed graph serializer, finite weighted verifier and N21 sparse
-- endpoint certificate owners. No postulates or oracle-cost flags.
-- This integration owner does NOT declare --safe until upstream graph
-- modules have a transitive-safe import closure and a kernel receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (∣_∣)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.List.Base using (List; []; _∷_; _++_; length)
import Data.List.Properties as ListP
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (sym)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Zigzag
import DASHI.Mathematics.Complexity.Karp21GammaSignedListRoundTripExact as Signed
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21SparseGraphWordNPBoundaryExact as Graph
import DASHI.Mathematics.Complexity.Karp21GammaZigzagWordEncodeExact as Encode

------------------------------------------------------------------------
-- Elementary list facts, proved by structural recursion. These avoid
-- depending on a version-specific stdlib append-bound lemma.
------------------------------------------------------------------------

appendLeftLengthLower :
  ∀ {A : Set} (prefix suffix : List A) →
  length prefix ≤ length (prefix ++ suffix)
appendLeftLengthLower [] suffix = z≤n
appendLeftLengthLower (_ ∷ rest) suffix =
  s≤s (appendLeftLengthLower rest suffix)

naturalAtMostSuccessor : (n : Nat) → n ≤ suc n
naturalAtMostSuccessor zero = z≤n
naturalAtMostSuccessor (suc n) =
  s≤s (naturalAtMostSuccessor n)

appendRightLengthLower :
  ∀ {A : Set} (prefix suffix : List A) →
  length suffix ≤ length (prefix ++ suffix)
appendRightLengthLower [] suffix = NatP.≤-refl
appendRightLengthLower (_ ∷ rest) suffix =
  NatP.≤-trans
    (appendRightLengthLower rest suffix)
    (naturalAtMostSuccessor (length (rest ++ suffix)))

bitWordLengthSameObject :
  (bits : Word.BitWord) →
  length bits ≡ Word.encodingSize bits
bitWordLengthSameObject [] = refl
bitWordLengthSameObject (_ ∷ rest)
  rewrite bitWordLengthSameObject rest = refl

------------------------------------------------------------------------
-- Each original signed edge contains at least two gamma endpoint bits.
-- Its (possibly negative or zero) weight contributes extra bits.
------------------------------------------------------------------------

encodedEdgeAtLeastTwoBits :
  ∀ {n} (edge : Cut.SignedUndirectedEdge n) →
  suc (suc zero) ≤ length (Encode.encodeEdgeWord edge)
encodedEdgeAtLeastTwoBits edge =
  NatP.≤-trans
    (NatP.+-mono-≤
      (Signed.gammaNatHasBit (Fin.toℕ (Cut.first edge)))
      (Signed.gammaNatHasBit (Fin.toℕ (Cut.second edge))))
    (NatP.≤-trans
      (NatP.+-mono-≤ NatP.≤-refl
        (appendLeftLengthLower
          (Gamma.encodeGammaNat (Fin.toℕ (Cut.second edge)))
          (Encode.encodeSignedGamma (Cut.weight edge))))
      (NatP.≤-reflexive
        (sym (ListP.length-++
          (Gamma.encodeGammaNat (Fin.toℕ (Cut.first edge)))
          (Gamma.encodeGammaNat (Fin.toℕ (Cut.second edge))
            ++ Encode.encodeSignedGamma (Cut.weight edge))))))

------------------------------------------------------------------------
-- Use the ORIGINAL Sparse.twoPerEdge and the original edge list.
------------------------------------------------------------------------

encodedEdgeWordsAtLeastSparseBits :
  ∀ {n} (edges : List (Cut.SignedUndirectedEdge n)) →
  Sparse.twoPerEdge (length edges)
    ≤ length (Encode.encodeEdgeWords edges)
encodedEdgeWordsAtLeastSparseBits [] = z≤n
encodedEdgeWordsAtLeastSparseBits (edge ∷ rest)
  rewrite ListP.length-++ (Encode.encodeEdgeWord edge)
    (Encode.encodeEdgeWords rest) =
  NatP.+-mono-≤
    (encodedEdgeAtLeastTwoBits edge)
    (encodedEdgeWordsAtLeastSparseBits rest)

------------------------------------------------------------------------
-- Prefix count fields and positive W can only add bits. The theorem
-- holds for every typed graph, including empty lists and sparse graphs
-- whose declared vertex count is exponentially larger than the word.
------------------------------------------------------------------------

encodedGraphAtLeastSparseBits :
  (instance : Graph.GraphInstance) →
  Sparse.twoPerEdge (length (Cut.edges (proj₂ instance)))
    ≤ Word.encodingSize (Encode.encodeGraphWord instance)
encodedGraphAtLeastSparseBits (n , graph) =
  NatP.≤-trans
    (encodedEdgeWordsAtLeastSparseBits (Cut.edges graph))
    (NatP.≤-trans
      (appendLeftLengthLower
        (Encode.encodeEdgeWords (Cut.edges graph))
        (Gamma.encodeGammaNat (∣ Cut.threshold graph ∣)))
      (NatP.≤-trans
        (appendRightLengthLower
          (Gamma.encodeGammaNat (length (Cut.edges graph)))
          (Encode.encodeEdgeWords (Cut.edges graph)
            ++ Gamma.encodeGammaNat (∣ Cut.threshold graph ∣)))
        (NatP.≤-trans
          (appendRightLengthLower
            (Gamma.encodeGammaNat n)
            (Gamma.encodeGammaNat (length (Cut.edges graph))
              ++ Encode.encodeEdgeWords (Cut.edges graph)
              ++ Gamma.encodeGammaNat (∣ Cut.threshold graph ∣)))
          (NatP.≤-reflexive
            (bitWordLengthSameObject
              (Encode.encodeGraphWord (n , graph)))))))


------------------------------------------------------------------------
-- Original graph decoder's separate m*3 parse guard. Each listed edge
-- literally contains gamma(u), gamma(v), gamma(zigzag(weight)).
-- All THREE fields are nonempty, including zero and negative weights.
------------------------------------------------------------------------

encodedEdgeAtLeastThreeBits :
  ∀ {n} (edge : Cut.SignedUndirectedEdge n) →
  suc (suc (suc zero)) ≤ length (Encode.encodeEdgeWord edge)
encodedEdgeAtLeastThreeBits edge
  rewrite ListP.length-++
    (Gamma.encodeGammaNat (Fin.toℕ (Cut.first edge)))
    (Gamma.encodeGammaNat (Fin.toℕ (Cut.second edge))
      ++ Encode.encodeSignedGamma (Cut.weight edge))
        | ListP.length-++
    (Gamma.encodeGammaNat (Fin.toℕ (Cut.second edge)))
    (Encode.encodeSignedGamma (Cut.weight edge)) =
  NatP.+-mono-≤
    (Signed.gammaNatHasBit (Fin.toℕ (Cut.first edge)))
    (NatP.+-mono-≤
      (Signed.gammaNatHasBit (Fin.toℕ (Cut.second edge)))
      (Signed.gammaNatHasBit
        (Zigzag.zigzag (Cut.weight edge))))

encodedEdgeWordsAtLeastTripleBits :
  ∀ {n} (edges : List (Cut.SignedUndirectedEdge n)) →
  (length edges * suc (suc (suc zero)))
    ≤ length (Encode.encodeEdgeWords edges)
encodedEdgeWordsAtLeastTripleBits [] = z≤n
encodedEdgeWordsAtLeastTripleBits (edge ∷ rest)
  rewrite ListP.length-++ (Encode.encodeEdgeWord edge)
    (Encode.encodeEdgeWords rest) =
  NatP.+-mono-≤
    (encodedEdgeAtLeastThreeBits edge)
    (encodedEdgeWordsAtLeastTripleBits rest)

-- The positive threshold field comes after all edges, so the exact
-- parser guard is implied by the actual source-generated serialization.
encodedGraphEdgeParserBudget :
  (instance : Graph.GraphInstance) →
  (length (Cut.edges (proj₂ instance)) * suc (suc (suc zero)))
    ≤ length
       (Encode.encodeEdgeWords (Cut.edges (proj₂ instance))
       ++ Gamma.encodeGammaNat (∣ Cut.threshold (proj₂ instance) ∣))
encodedGraphEdgeParserBudget (n , graph) =
  NatP.≤-trans
    (encodedEdgeWordsAtLeastTripleBits (Cut.edges graph))
    (appendLeftLengthLower
      (Encode.encodeEdgeWords (Cut.edges graph))
      (Gamma.encodeGammaNat (∣ Cut.threshold graph ∣)))

