module DASHI.Mathematics.Complexity.Karp21NativeWholeRawGraphWordExact where

------------------------------------------------------------------------
-- P0-B/E: SAME ORIGINAL FIN-FREE RAW GRAPH WORD, ACTUAL native
-- signed weight bits, ACTUAL native strictly-positive threshold bits.
--
-- Literal input format from Karp21FinFreeRawSparseWordVerifierExact:
-- gamma(n), gamma(m), m x [gamma(u), gamma(v), gamma(zigzag(w))],
-- gamma(W), NO suffix. The source n,m,endpoint gamma readers and
-- source Nat validation are reused exactly, NOT replaced with an
-- unproven binary endpoint model. Edge WEIGHTS and THRESHOLD are
-- already read by their actual native bit parsers.
--
-- No claim that this is a physically bit-native endpoint machine:
-- nativeOriginalGraphWordFieldsSame and the true bit tape clock
-- remain independent theorem gates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary.Decidable.Core using (yes; no)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FractranPairedBinaryTraceExact as Paired
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeRawEdgeStreamExact as Edges
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original

record NativeParsedRawGraph : Set where
  constructor native-parsed-raw-graph
  field
    originalVertices : Nat
    nativePairedEdges : List Paired.PairedRawEdge
    nativeThresholdLE : Word.BitWord
open NativeParsedRawGraph public

-- The strict source 3*m guard, original endpoint u/v grammar,
-- source original raw-edge validation and no-suffix policy all remain.
readNativeWholeRawGraphWord :
  Word.BitWord → Maybe NativeParsedRawGraph
readNativeWholeRawGraphWord word with Gamma.readGamma word
... | nothing = nothing
... | just (n , afterN) with Gamma.readGamma afterN
... | nothing = nothing
... | just (m , afterM)
  with NatP._≤?_ (m * suc (suc (suc zero))) (length afterM)
... | no _ = nothing
... | yes _
  with Edges.readNativePairedRawEdges m afterM
... | nothing = nothing
... | just (paired , afterEdges)
  with Positive.readPositiveGammaLE afterEdges
... | nothing = nothing
... | just (thresholdLE , _ ∷ _) = nothing
... | just (thresholdLE , [])
  with Original.validRawEdges n Graph.noPrevious
    (Paired.rawFromPairs paired)
... | false = nothing
... | true =
  just (native-parsed-raw-graph n paired thresholdLE)

-- Proof-side original graph payload. Runtime retains binary signed
-- weight tokens and the LE threshold register.
originalRawGraphObservation :
  NativeParsedRawGraph → Original.ParsedRawGraph
originalRawGraphObservation
  (native-parsed-raw-graph n paired thresholdLE) =
  Original.parsed-raw-graph
    n (Paired.rawFromPairs paired) (Value.valueLE thresholdLE)

observeNativeWholeRawGraphWord :
  Word.BitWord → Maybe Original.ParsedRawGraph
observeNativeWholeRawGraphWord word
  with readNativeWholeRawGraphWord word
... | nothing = nothing
... | just parsed = just (originalRawGraphObservation parsed)

-- Small original empty graph: gamma(0), gamma(0), gamma(1).
nativeEmptyPositiveGraphFrameExact :
  readNativeWholeRawGraphWord
    (true ∷ true ∷ false ∷ true ∷ false ∷ [])
  ≡ just (native-parsed-raw-graph
      zero [] (true ∷ false ∷ []))
nativeEmptyPositiveGraphFrameExact = refl

-- The ZERO threshold is rejected by the same native parser.
nativeZeroPositiveThresholdRejected :
  readNativeWholeRawGraphWord
    (true ∷ true ∷ true ∷ [])
    ≡ nothing
nativeZeroPositiveThresholdRejected = refl

-- Source failing graph decode and native graph decode SAME-WORD
-- reflection is the remaining all-word theorem:
--
-- nativeOriginalGraphWordFieldsSame :
--   ∀ word →
--   observeNativeWholeRawGraphWord word
--     ≡ Original.readRawGraphWord word
--
-- This requires the actual raw-edge-stream theorem, all-word strict
-- positive-threshold parser equality and the original validator
-- conjunction, not a new validator or invented field isomorphism.
