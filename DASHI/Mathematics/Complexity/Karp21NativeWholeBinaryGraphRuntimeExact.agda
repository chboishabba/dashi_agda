module DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact where

------------------------------------------------------------------------
-- P0-B/F original signed N21 WHOLE GRAPH BIT-NATIVE RUNTIME.
--
-- Unlike the original Fin-free graph reader, this executable does
-- NOT construct a unary Nat n, m, u or v from gamma-encoded input.
--   n,m = native unsigned gamma LE bit registers;
--   3*m <= length(remaining) is checked BEFORE any edge loop via
--       binary ripple addition and the actual LE binary comparator;
--   each u/v field is native LE binary; w is signed binary payload;
--   loop fuel is bounded by the ACTUAL input suffix length, not m;
--   strict u<v<n and increasing (u,v) are binary comparisons;
--   W is actual source strictly-positive gamma predecessor LE;
--   no trailing suffix is accepted.
--
-- A full same-original-WORD theorem and original binary endpoint-
-- history scoring are still required before calling B6 closed.
-- This is real executable code, not merely proof-side ℤ/Nat observation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21NativeBinaryHeaderBudgetExact as Header
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointValidatorExact as Valid
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive

record NativeWholeBinaryGraph : Set where
  constructor whole-binary-graph
  field
    verticesLE : Word.BitWord
    binaryEdges : List Edge.BinaryRawEdge
    thresholdLE : Word.BitWord
open NativeWholeBinaryGraph public

-- Decrement m as an actual bit-register, never by unary Nat recursion.
-- An input-length fuel bounds work for malformed words even if
-- gamma(m) mathematically denotes an astronomical edge count.
-- This owner does not claim the fuel is a physical tape-step clock.
readBinaryRawEdgesFuel :
  Nat → Word.BitWord → Word.BitWord →
  Maybe (List Edge.BinaryRawEdge × Word.BitWord)
readBinaryRawEdgesFuel zero mLE word
  with Positive.anyOne mLE
... | false = just ([] , word)
... | true = nothing
readBinaryRawEdgesFuel (suc remainingFuel) mLE word
  with Positive.anyOne mLE
... | false = just ([] , word)
... | true with Edge.readOneBinaryRawEdge word
... | nothing = nothing
... | just (edge , rest)
  with readBinaryRawEdgesFuel remainingFuel
    (Positive.predecessorLE mLE) rest
... | nothing = nothing
... | just (edges , suffix) =
  just (edge ∷ edges , suffix)

-- The whole original source grammar, with every potentially
-- enormous source gamma address/count kept as a native binary word.
readNativeWholeBinaryGraphWord :
  Word.BitWord → Maybe NativeWholeBinaryGraph
readNativeWholeBinaryGraphWord word
  with Header.readNativeBinaryBudgetedHeader word
... | nothing = nothing
... | just (Header.binary-header nLE mLE afterM)
  with readBinaryRawEdgesFuel (length afterM) mLE afterM
... | nothing = nothing
... | just (edges , afterEdges)
  with Positive.readPositiveGammaLE afterEdges
... | nothing = nothing
... | just (thresholdLE , _ ∷ _) = nothing
... | just (thresholdLE , [])
  with Valid.validNativeBinaryEdges nLE Valid.noPrevious edges
... | false = nothing
... | true =
  just (whole-binary-graph nLE edges thresholdLE)
