module DASHI.Mathematics.Complexity.Karp21NativeParsedRawAcceptanceExact where

------------------------------------------------------------------------
-- P0-E: genuine original signed N21 acceptance on SOURCE-PARSED
-- native signed raw-edge streams and original certificate bits.
--
-- No independent semantic scorer: actual Paired.nativePairedLedger
-- uses binary ripple registers and original endpoint-consistency.
-- Actual Positive.meetsOriginalPositiveThreshold performs the
-- native binary add/atLeast test. The original RHS is the exact
-- Runtime.rawSparseScore/Int._≤ᵇ_ positive threshold on the SAME
-- source raw edges and original certificate.
--
-- This is intentionally narrower than all-word original graph
-- verification: field parsing and strict graph validity still need
-- to be consumed by a whole-word theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; [])
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
import Data.Integer.Base as Int
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21FractranPairedBinaryTraceExact as Paired
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeRawEdgeStreamExact as NativeEdges
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21NativeLedgerOriginalRawScoreExact as LedgerScore
import DASHI.Mathematics.Complexity.Karp21NativeThresholdOriginalSignedDecisionExact as Threshold
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value

-- The original certificate is used unchanged; original weight
-- alignment comes from the actual native signed gamma edge parser.
nativeParsedRawAccepts :
  List Paired.PairedRawEdge → Word.BitWord → Word.BitWord → Bool
nativeParsedRawAccepts paired cert thresholdLE
  with Paired.nativePairedLedger paired cert []
... | nothing = false
... | just ledger =
  Positive.meetsOriginalPositiveThreshold ledger thresholdLE

originalParsedRawAccepts :
  List Paired.PairedRawEdge → Word.BitWord → Nat → Bool
originalParsedRawAccepts paired cert threshold
  with Original.rawSparseScore (Paired.rawFromPairs paired) cert []
... | nothing = false
... | just score = Int._≤ᵇ_ (Int.+ threshold) score

-- Actual binary signed ledger threshold = original signed raw
-- Max-Cut score >= W on every grammar-parsed raw signed-edge stream,
-- including all malformed/overlong original certificate words.
karpNativeParsedRawAcceptanceSameOriginal :
  (count : Nat)
  (source : Word.BitWord)
  (paired : List Paired.PairedRawEdge)
  (suffix certificate thresholdLE : Word.BitWord) →
  NativeEdges.readNativePairedRawEdges count source
    ≡ just (paired , suffix) →
  nativeParsedRawAccepts paired certificate thresholdLE
    ≡ originalParsedRawAccepts
      paired certificate
      (Value.valueLE thresholdLE)
karpNativeParsedRawAcceptanceSameOriginal
  count source paired suffix certificate thresholdLE parsed
  with Paired.nativePairedLedger paired certificate []
     | LedgerScore.nativeSignedLedgerIntegerEqualsOriginalRawSparseScore
         count source paired suffix certificate [] parsed
... | nothing | equation rewrite sym equation = refl
... | just ledger | equation
  rewrite sym equation
        | Threshold.karpNativeThresholdDecisionSameOriginal
            ledger thresholdLE = refl
