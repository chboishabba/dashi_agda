module DASHI.Mathematics.Complexity.Karp21FractranOriginalTypedTraceAcceptanceExact where

------------------------------------------------------------------------
-- Original Karp N21 entire-word selected-edge trace ↔ typed verifier.
--
-- The trace evaluator uses the original raw graph parser and signed ℤ
-- weights, not a new graph language or a binary-value oracle.
-- This composes two genuine SOURCE-OWNED all-word equalities:
--
--  1. selected-trace replay = original Fin-free rawSparseScore Bool
--  2. original Fin-free Bool = original typed LiteralN21 Bool.
--
-- All graph words/certificate words, including malformed ones.
--
-- Not a statement about the still-unproved native-binary FRACTRAN
-- execution or about a polynomial-time Turing machine.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21FractranOriginalRawTraceReplayExact as Trace
import DASHI.Mathematics.Complexity.Karp21FinFreeAllWordDecoderAgreementExact as Original
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph

karpOriginalTraceSameTypedN21AllWords :
  (word certificate : Word.BitWord) →
  Trace.verifyOriginalGraphWordByTrace word certificate
    ≡ Graph.LiteralN21.verifyCanonicalSparseGraphWord word certificate
karpOriginalTraceSameTypedN21AllWords word certificate =
  trans
    (Trace.karpOriginalRawTraceAllWordAcceptance word certificate)
    (Original.n21FinFreeVerifierSameWord word certificate)
