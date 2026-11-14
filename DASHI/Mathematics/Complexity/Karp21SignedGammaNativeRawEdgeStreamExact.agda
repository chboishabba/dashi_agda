module DASHI.Mathematics.Complexity.Karp21SignedGammaNativeRawEdgeStreamExact where

------------------------------------------------------------------------
-- Karp P0-B: source ORIGINAL N21 raw graph-edge stream, with the
-- ACTUAL native signed binary token reader substituted for the
-- original signed-ℤ gamma field, retaining the exact original graph
-- endpoints/cursor and original malformed-word rejection.
--
-- This is no fresh graph language, no unknown decoder oracle.
-- Each token is paired with the exact original RawEdge read from
-- the SAME gamma input, including signed weight and remaining suffix.
--
-- Limit: endpoint gamma readers here are still the source's original
-- Nat-producing parser. The bit-native endpoint representation/clock
-- and the full graph header/validation/threshold remain separate P0.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeOriginalValueExact as Value
import DASHI.Mathematics.Complexity.Karp21FractranPairedBinaryTraceExact as Pair

readOneNativePairedRawEdge :
  Word.BitWord → Maybe (Pair.PairedRawEdge × Word.BitWord)
readOneNativePairedRawEdge word with Gamma.readGamma word
... | nothing = nothing
... | just (u , afterU) with Gamma.readGamma afterU
...   | nothing = nothing
...   | just (v , afterV) with Signed.readSignedBinary afterV
...     | nothing = nothing
...     | just (token , suffix) =
  just ((Graph.raw-edge u v (Value.interpretNativeToken token) , token)
      , suffix)

originalRawFromNativeOne :
  Maybe (Pair.PairedRawEdge × Word.BitWord) →
  Maybe (Graph.RawEdge × Word.BitWord)
originalRawFromNativeOne nothing = nothing
originalRawFromNativeOne (just ((edge , token) , suffix)) =
  just (edge , suffix)

-- Every original one-edge word, including malformed and truncated,
-- has IDENTICAL output raw endpoints, signed ℤ weight and suffix
-- under the paired binary-token executable weight reader.
oneNativePairedRawEdgeSameOriginal :
  (word : Word.BitWord) →
  originalRawFromNativeOne (readOneNativePairedRawEdge word)
    ≡ Graph.readOneRawEdge word
oneNativePairedRawEdgeSameOriginal word
  with Gamma.readGamma word
... | nothing = refl
... | just (u , afterU) with Gamma.readGamma afterU
...   | nothing = refl
...   | just (v , afterV)
  rewrite sym (Value.karpNativeSignedTokenValueMatchesOriginal afterV)
  with Signed.readSignedBinary afterV
...     | nothing = refl
...     | just (token , suffix) = refl

-- EXACT original graph edge-count recursion, with native signed weight
-- tokens paired at every actual source edge. No guessed list length.
readNativePairedRawEdges :
  Nat → Word.BitWord →
  Maybe (List Pair.PairedRawEdge × Word.BitWord)
readNativePairedRawEdges zero word = just ([] , word)
readNativePairedRawEdges (suc count) word
  with readOneNativePairedRawEdge word
... | nothing = nothing
... | just (edge , rest)
  with readNativePairedRawEdges count rest
...   | nothing = nothing
...   | just (edges , suffix) =
  just (edge ∷ edges , suffix)

originalRawFromNativeStream :
  Maybe (List Pair.PairedRawEdge × Word.BitWord) →
  Maybe (List Graph.RawEdge × Word.BitWord)
originalRawFromNativeStream nothing = nothing
originalRawFromNativeStream (just (paired , suffix)) =
  just (Pair.rawFromPairs paired , suffix)

-- Full original readRawEdges(m) stream correspondence: identical raw
-- edge identities, original signed weights, and final suffix, on
-- every word and m including all intermediate parse failures.
nativePairedRawEdgesSameOriginal :
  (count : Nat) (word : Word.BitWord) →
  originalRawFromNativeStream (readNativePairedRawEdges count word)
    ≡ Graph.readRawEdges count word
nativePairedRawEdgesSameOriginal zero word = refl
nativePairedRawEdgesSameOriginal (suc count) word
  with readOneNativePairedRawEdge word
... | nothing
  rewrite sym (oneNativePairedRawEdgeSameOriginal word) = refl
... | just (edge , rest)
  rewrite sym (oneNativePairedRawEdgeSameOriginal word)
  with readNativePairedRawEdges count rest
...   | nothing
  rewrite sym (nativePairedRawEdgesSameOriginal count rest) = refl
...   | just (edges , suffix)
  rewrite sym (nativePairedRawEdgesSameOriginal count rest) = refl
