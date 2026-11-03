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

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (∣_∣)
open import Data.Nat.Base using (_≤_; z≤n)
import Data.Nat.Properties as NatP
open import Data.List.Base using (List; []; _∷_; _++_; length)
import Data.List.Properties as ListP
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (sym)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaSignedListRoundTripExact as Signed
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21SparseGraphWordNPBoundaryExact as Graph
import DASHI.Mathematics.Complexity.Karp21GammaZigzagWordEncodeExact as Encode

------------------------------------------------------------------------
-- One gamma bit for each endpoint, even for a huge declared vertex n.
------------------------------------------------------------------------

encodedEdgeAtLeastTwoBits :
  ∀ {n} (edge : Cut.SignedUndirectedEdge n) →
  suc (suc zero) ≤ length (Encode.encodeEdgeWord edge)
encodedEdgeAtLeastTwoBits edge =
  NatP.≤-trans
    (NatP.+-mono-≤
      (Signed.gammaNatHasBit (Fin.toℕ (Cut.first edge)))
      (NatP.≤-trans
        (Signed.gammaNatHasBit (Fin.toℕ (Cut.second edge)))
        (ListP.length-++-≤ˡ
          (Gamma.encodeGammaNat (Fin.toℕ (Cut.second edge))))))
    (NatP.≤-reflexive
      (sym (ListP.length-++
        (Gamma.encodeGammaNat (Fin.toℕ (Cut.first edge))))))

------------------------------------------------------------------------
-- Exactly the original Sparse.twoPerEdge, not a substitute 2*m
-- arithmetic definition. No assumption of nonempty edge lists.
------------------------------------------------------------------------

encodedEdgeWordsAtLeastSparseBits :
  ∀ {n} (edges : List (Cut.SignedUndirectedEdge n)) →
  Sparse.twoPerEdge (length edges)
    ≤ length (Encode.encodeEdgeWords edges)
encodedEdgeWordsAtLeastSparseBits [] = z≤n
encodedEdgeWordsAtLeastSparseBits (edge ∷ rest)
  rewrite ListP.length-++ (Encode.encodeEdgeWord edge) =
  NatP.+-mono-≤
    (encodedEdgeAtLeastTwoBits edge)
    (encodedEdgeWordsAtLeastSparseBits rest)

------------------------------------------------------------------------
-- Graph headers and target W only INCREASE wire length.
-- This is the original graph instance's literal encoder, including
-- signed edge weights, positive threshold and declared vertex count.
------------------------------------------------------------------------

encodedGraphAtLeastSparseBits :
  (instance : Graph.GraphInstance) →
  Sparse.twoPerEdge (length (Cut.edges (proj₂ instance)))
    ≤ Word.encodingSize (Encode.encodeGraphWord instance)
encodedGraphAtLeastSparseBits (n , graph) =
  NatP.≤-trans
    (encodedEdgeWordsAtLeastSparseBits (Cut.edges graph))
    (NatP.≤-trans
      (ListP.length-++-≤ˡ
        (Encode.encodeEdgeWords (Cut.edges graph)))
      (NatP.≤-trans
        (ListP.length-++-≤ʳ
          (Encode.encodeEdgeWords (Cut.edges graph)
            ++ Gamma.encodeGammaNat
              (∣ Cut.threshold graph ∣))
          {xs = Gamma.encodeGammaNat (length (Cut.edges graph))})
        (ListP.length-++-≤ʳ
          (Gamma.encodeGammaNat (length (Cut.edges graph))
            ++ Encode.encodeEdgeWords (Cut.edges graph)
            ++ Gamma.encodeGammaNat
              (∣ Cut.threshold graph ∣))
          {xs = Gamma.encodeGammaNat n})))
