module DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact where

------------------------------------------------------------------------
-- P0-B/F: original signed N21 RAW EDGE with *real binary endpoints*.
--
-- Actual runtime paths use readGammaNatLE for u and v and actual
-- Signed.readSignedBinary for w. No source Gamma.readGamma Nat address
-- is evaluated by this executable raw-edge reader. Numerical
-- interpretation is in the proof-side observation ONLY.
-- Count m remains original Nat here: binary count/validation/physical
-- tape clock and canonical strict edge order are remaining gates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21NativeUnsignedEndpointBitReaderExact as Endpoint
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeOriginalValueExact as Weight
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Original

record BinaryRawEdge : Set where
  constructor binary-edge
  field
    sourceLE : Word.BitWord
    targetLE : Word.BitWord
    weightToken : Signed.SignedMagnitudeBits
open BinaryRawEdge public

-- Literal original gamma(u), gamma(v), signed gamma(w) wire grammar.
-- This executable reader produces no Nat addresses or integer weights.
readOneBinaryRawEdge :
  Word.BitWord → Maybe (BinaryRawEdge × Word.BitWord)
readOneBinaryRawEdge word
  with Endpoint.readGammaNatLE word
... | nothing = nothing
... | just (uLE , afterU)
  with Endpoint.readGammaNatLE afterU
... | nothing = nothing
... | just (vLE , afterV)
  with Signed.readSignedBinary afterV
... | nothing = nothing
... | just (w , suffix) =
  just (binary-edge uLE vLE w , suffix)

-- Mathematical observation only, not an executable Nat reconstruction.
originalEdgeObservation : BinaryRawEdge → Original.RawEdge
originalEdgeObservation (binary-edge u v w) =
  Original.raw-edge (Value.valueLE u) (Value.valueLE v)
    (Weight.interpretNativeToken w)

observeOneBinaryEdge :
  Maybe (BinaryRawEdge × Word.BitWord) →
  Maybe (Original.RawEdge × Word.BitWord)
observeOneBinaryEdge nothing = nothing
observeOneBinaryEdge (just (edge , suffix)) =
  just (originalEdgeObservation edge , suffix)

-- All malformed and successful original edge words, exact suffix.
-- The old original readOneRawEdge is used ONLY on the RHS of the proof.
oneBinaryEndpointRawEdgeSameOriginal :
  (word : Word.BitWord) →
  observeOneBinaryEdge (readOneBinaryRawEdge word)
    ≡ Original.readOneRawEdge word
oneBinaryEndpointRawEdgeSameOriginal word
  with Endpoint.readGammaNatLE word
     | Endpoint.nativeUnsignedEndpointSameOriginal word
... | nothing | firstEq rewrite sym firstEq = refl
... | just (u , afterU) | firstEq
  rewrite sym firstEq
  with Endpoint.readGammaNatLE afterU
     | Endpoint.nativeUnsignedEndpointSameOriginal afterU
... | nothing | secondEq rewrite sym secondEq = refl
... | just (v , afterV) | secondEq
  rewrite sym secondEq
  with Signed.readSignedBinary afterV
     | Weight.karpNativeSignedTokenValueMatchesOriginal afterV
... | nothing | weightEq rewrite sym weightEq = refl
... | just (w , suffix) | weightEq
  rewrite sym weightEq = refl

readBinaryRawEdges :
  Nat → Word.BitWord → Maybe (List BinaryRawEdge × Word.BitWord)
readBinaryRawEdges zero word = just ([] , word)
readBinaryRawEdges (suc count) word with readOneBinaryRawEdge word
... | nothing = nothing
... | just (edge , rest) with readBinaryRawEdges count rest
... | nothing = nothing
... | just (edges , suffix) = just (edge ∷ edges , suffix)

originalEdgeListObservation :
  List BinaryRawEdge → List Original.RawEdge
originalEdgeListObservation [] = []
originalEdgeListObservation (edge ∷ rest) =
  originalEdgeObservation edge ∷ originalEdgeListObservation rest

observeBinaryEdgeStream :
  Maybe (List BinaryRawEdge × Word.BitWord) →
  Maybe (List Original.RawEdge × Word.BitWord)
observeBinaryEdgeStream nothing = nothing
observeBinaryEdgeStream (just (edges , suffix)) =
  just (originalEdgeListObservation edges , suffix)

-- Same ORIGINAL counted raw-edge stream, all words/edge counts,
-- without runtime unary endpoint decoding. Count m is still Nat.
binaryEndpointRawEdgeStreamSameOriginal :
  (count : Nat) (word : Word.BitWord) →
  observeBinaryEdgeStream (readBinaryRawEdges count word)
    ≡ Original.readRawEdges count word
binaryEndpointRawEdgeStreamSameOriginal zero word = refl
binaryEndpointRawEdgeStreamSameOriginal (suc count) word
  with readOneBinaryRawEdge word
     | oneBinaryEndpointRawEdgeSameOriginal word
... | nothing | headEq rewrite sym headEq = refl
... | just (edge , rest) | headEq
  rewrite sym headEq
  with readBinaryRawEdges count rest
     | binaryEndpointRawEdgeStreamSameOriginal count rest
... | nothing | tailEq rewrite sym tailEq = refl
... | just (edges , suffix) | tailEq
  rewrite sym tailEq = refl
