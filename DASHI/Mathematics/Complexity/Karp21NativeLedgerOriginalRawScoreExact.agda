module DASHI.Mathematics.Complexity.Karp21NativeLedgerOriginalRawScoreExact where

------------------------------------------------------------------------
-- P0-C: close the mathematical SCORE observation of the ACTUAL
-- native two-lane binary accumulator on original parsed edge streams.
--
-- Source ownership chain (no replacement graph language):
--   original Gamma.readGamma u/v and Signed.readSignedBinary edge weight
--   -> readNativePairedRawEdges original count/cursor
--   -> original endpointConsistent/two-bit certificate selection
--   -> Ledger.accumulateSigned real native binary ripple adders
--   -> integerFromTwoLaneTotals proof-side observation
--   -> original Runtime.rawSparseScore signed ℤ result.
--
-- It is NOT yet the full validated original graph-word, physical
-- bit-Turing machine cost or FRACDASH transition proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Integer.Base using (ℤ)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21FractranPairedBinaryTraceExact as Paired
import DASHI.Mathematics.Complexity.Karp21NativeSelectedSignedScoreExact as SignedScore
import DASHI.Mathematics.Complexity.Karp21NativeLedgerIntegerScoreExact as IntegerLedger
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeRawEdgeStreamExact as NativeEdges
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger

observeOptionalNativeLedger : Maybe Ledger.SignedLedger → Maybe ℤ
observeOptionalNativeLedger nothing = nothing
observeOptionalNativeLedger (just ledger) =
  just (IntegerLedger.observeActualNativeLedger ledger)

-- All supplied raw-edge/token paired lists and certificate histories:
-- actual ledger-to-token trace score correspondence, including full
-- endpoint rejection; no numeric source alignment premise needed here.
nativeLedgerScoreMatchesNativeSelectedTrace :
  (paired : List Paired.PairedRawEdge)
  (bits : Word.BitWord)
  (history : List (Nat × Bool)) →
  observeOptionalNativeLedger
    (Paired.nativePairedLedger paired bits history)
    ≡ SignedScore.nativePairedScoreObservation paired bits history
nativeLedgerScoreMatchesNativeSelectedTrace paired bits history
  with Paired.selectPairedTrace paired bits history
... | nothing = refl
... | just selected =
  cong just
    (IntegerLedger.nativeSignedLedgerIntegerEqualsOriginalTraceScore
      (Paired.nativeProjection selected))

-- This is the SAME original rawSparseScore on edge lists taken from
-- the original gamma grammar with a native signed bit-token weight.
-- The theorem does not assume arbitrary pre-aligned tokens.
nativeSignedLedgerIntegerEqualsOriginalRawSparseScore :
  (count : Nat)
  (source : Word.BitWord)
  (paired : List Paired.PairedRawEdge)
  (suffix certificate : Word.BitWord)
  (history : List (Nat × Bool)) →
  NativeEdges.readNativePairedRawEdges count source
    ≡ just (paired , suffix) →
  observeOptionalNativeLedger
    (Paired.nativePairedLedger paired certificate history)
    ≡ Runtime.rawSparseScore
        (Paired.rawFromPairs paired) certificate history
nativeSignedLedgerIntegerEqualsOriginalRawSparseScore
  count source paired suffix certificate history parsed =
  trans
    (nativeLedgerScoreMatchesNativeSelectedTrace
      paired certificate history)
    (SignedScore.nativeRawStreamSignedScoreSameOriginal
      count source paired suffix certificate history parsed)
