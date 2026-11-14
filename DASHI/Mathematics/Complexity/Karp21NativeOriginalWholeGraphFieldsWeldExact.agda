module DASHI.Mathematics.Complexity.Karp21NativeOriginalWholeGraphFieldsWeldExact where

------------------------------------------------------------------------
-- P0-B/E: SAME ORIGINAL FIN-FREE GRAPH WORD ON ALL INPUT BITWORDS.
--
-- This composition pays the full original n/m header, m*3 short-word
-- guard, counted actual native signed raw-edge stream, strictly
-- positive native gamma(W), exact suffix, and original validRawEdges.
--
-- The proof is on the original Nat-bearing runtime graph observation.
-- Native endpoint addresses / graph header and source validation STILL
-- execute original Nat gamma; a true bit-TM endpoint clock is OPEN.
-- Exact-head Agda kernel acceptance is a separate gate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.List.Base using (List; length)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (trans; sym)
open import Relation.Nullary.Decidable.Core using (yes; no)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FractranPairedBinaryTraceExact as Paired
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeRawEdgeStreamExact as NativeEdges
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21NativePositiveThresholdNumericFrameExact as ThresholdWeld
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original
import DASHI.Mathematics.Complexity.Karp21NativeWholeRawGraphWordExact as Native

-- Factor the original post-raw-edge terminal into an independent
-- exact source function so positive-gamma parser equivalence can be
-- consumed without replacing the original validator.
originalTerminal :
  Nat → List Graph.RawEdge → Word.BitWord →
  Maybe Original.ParsedRawGraph
originalTerminal n edges bits with Gamma.readGamma bits
... | nothing = nothing
... | just (zero , suffix) = nothing
... | just (suc threshold , _ ∷ _) = nothing
... | just (suc threshold , [])
  with Original.validRawEdges n Graph.noPrevious edges
... | false = nothing
... | true =
  just (Original.parsed-raw-graph n edges (suc threshold))

strictTerminal :
  Nat → List Graph.RawEdge → Word.BitWord →
  Maybe Original.ParsedRawGraph
strictTerminal n edges bits
  with ThresholdWeld.originalStrictPositiveGamma bits
... | nothing = nothing
... | just (threshold , _ ∷ _) = nothing
... | just (threshold , [])
  with Original.validRawEdges n Graph.noPrevious edges
... | false = nothing
... | true =
  just (Original.parsed-raw-graph n edges threshold)

sourceTerminalSameStrict :
  (n : Nat) (edges : List Graph.RawEdge) (bits : Word.BitWord) →
  originalTerminal n edges bits ≡ strictTerminal n edges bits
sourceTerminalSameStrict n edges bits with Gamma.readGamma bits
... | nothing = refl
... | just (zero , suffix) = refl
... | just (suc threshold , _ ∷ _) = refl
... | just (suc threshold , [])
  with Original.validRawEdges n Graph.noPrevious edges
... | false = refl
... | true = refl

nativeTerminal :
  Nat → List Paired.PairedRawEdge → Word.BitWord →
  Maybe Original.ParsedRawGraph
nativeTerminal n paired bits
  with Positive.readPositiveGammaLE bits
... | nothing = nothing
... | just (thresholdLE , _ ∷ _) = nothing
... | just (thresholdLE , [])
  with Original.validRawEdges n Graph.noPrevious
    (Paired.rawFromPairs paired)
... | false = nothing
... | true =
  just (Original.parsed-raw-graph n
    (Paired.rawFromPairs paired)
    (Value.valueLE thresholdLE))

-- Here the actual native Positive.readPositiveGammaLE result is
-- interpreted in Nat; source strict positive gamma result is the
-- same Nat and suffix on EVERY word, including failure.
nativeTerminalSameStrict :
  (n : Nat) (paired : List Paired.PairedRawEdge)
  (bits : Word.BitWord) →
  nativeTerminal n paired bits ≡
    strictTerminal n (Paired.rawFromPairs paired) bits
nativeTerminalSameStrict n paired bits
  rewrite sym (ThresholdWeld.nativePositiveThresholdParserSameOriginal bits)
  with Positive.readPositiveGammaLE bits
... | nothing = refl
... | just (thresholdLE , _ ∷ _) = refl
... | just (thresholdLE , [])
  with Original.validRawEdges n Graph.noPrevious
    (Paired.rawFromPairs paired)
... | false = refl
... | true = refl

-- This is the original *entire* graph-word parse, not just an
-- arbitrary supplied raw-edge list. Exact source n/m, m*3 guard,
-- native signed edge cursor, strictly-positive native threshold,
-- strict edge validation and no-suffix policy all occur on WORD.
nativeOriginalGraphWordFieldsSame :
  (word : Word.BitWord) →
  Native.observeNativeWholeRawGraphWord word
    ≡ Original.readRawGraphWord word
nativeOriginalGraphWordFieldsSame word
  with Gamma.readGamma word
... | nothing = refl
... | just (n , afterN)
  with Gamma.readGamma afterN
... | nothing = refl
... | just (m , afterM)
  with NatP._≤?_ (m * suc (suc (suc zero))) (length afterM)
... | no _ = refl
... | yes _
  with NativeEdges.readNativePairedRawEdges m afterM
     | NativeEdges.nativePairedRawEdgesSameOriginal m afterM
... | nothing | edgeEq rewrite sym edgeEq = refl
... | just (paired , afterEdges) | edgeEq
  rewrite sym edgeEq =
  trans
    (nativeTerminalSameStrict n paired afterEdges)
    (sym (sourceTerminalSameStrict
      n (Paired.rawFromPairs paired) afterEdges))
