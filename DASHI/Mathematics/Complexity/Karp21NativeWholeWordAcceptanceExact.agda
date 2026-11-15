module DASHI.Mathematics.Complexity.Karp21NativeWholeWordAcceptanceExact where

------------------------------------------------------------------------
-- P0-E ORIGINAL N21 SAME-WORD ACCEPTANCE: actual source complete graph.
--
-- Compose actual native signed gamma edge/strict-threshold graph parser,
-- the proven whole original graph-word field weld, and ACTUAL two-lane
-- binary signed threshold acceptance, against the original
-- FinFree.verifyFinFreeSparseGraphWord for EVERY input word/certificate.
--
-- No substitute graph language, no trusted oracle of aligned edges.
-- Important caveat: native header/endpoints still run original unary
-- Gamma.readGamma; this proves SEMANTIC alignment only, never a
-- polynomial bit-Turing-machine bound or PR.InNP.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
open import Relation.Nullary.Decidable.Core using (yes; no)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeRawEdgeStreamExact as Edges
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21NativeWholeRawGraphWordExact as Native
import DASHI.Mathematics.Complexity.Karp21FractranPairedBinaryTraceExact as Paired
import DASHI.Mathematics.Complexity.Karp21NativeOriginalWholeGraphFieldsWeldExact as Fields
import DASHI.Mathematics.Complexity.Karp21NativeParsedRawAcceptanceExact as Accepted
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original

-- Actual whole-word native parser, actual signed binary ledger and
-- actual bitwise positive-threshold comparator. Only acceptance is
-- observed as Bool, and no unary integer executes in the selected
-- native ledger/threshold branch.
nativeWholeWordAccepts :
  Word.BitWord → Word.BitWord → Bool
nativeWholeWordAccepts word certificate
  with Native.readNativeWholeRawGraphWord word
... | nothing = false
... | just (Native.native-parsed-raw-graph n paired thresholdLE) =
  Accepted.nativeParsedRawAccepts paired certificate thresholdLE

-- Proof receipt extracted from the actual full original wire parser:
-- its edge count, cursor and suffix are existentially reconstructed
-- from successful source execution, never arbitrarily supplied.
RawEdgeParseReceipt : Native.NativeParsedRawGraph → Set
RawEdgeParseReceipt parsed =
  Σ Nat (λ m →
    Σ Word.BitWord (λ afterM →
      Σ Word.BitWord (λ afterEdges →
        Edges.readNativePairedRawEdges m afterM
          ≡ just (Native.nativePairedEdges parsed , afterEdges))))

nativeWholeSuccessContainsActualEdgeReceipt :
  (word : Word.BitWord)
  (parsed : Native.NativeParsedRawGraph) →
  Native.readNativeWholeRawGraphWord word ≡ just parsed →
  RawEdgeParseReceipt parsed
nativeWholeSuccessContainsActualEdgeReceipt word parsed successful
  with Gamma.readGamma word
... | nothing with successful
... | ()
... | just (n , afterN)
  with Gamma.readGamma afterN
... | nothing with successful
... | ()
... | just (m , afterM)
  with NatP._≤?_ (m * suc (suc (suc zero))) (length afterM)
... | no _ with successful
... | ()
... | yes _
  with Edges.readNativePairedRawEdges m afterM in parsedEdges
... | nothing with successful
... | ()
... | just (paired , afterEdges)
  with Positive.readPositiveGammaLE afterEdges
... | nothing with successful
... | ()
... | just (thresholdLE , _ ∷ _) with successful
... | ()
... | just (thresholdLE , [])
  with Original.validRawEdges n Graph.noPrevious
    (Paired.rawFromPairs paired)
... | false with successful
... | ()
... | true with successful
... | refl =
  m , (afterM , (afterEdges , parsedEdges))

-- Original source verification is reached only through the same
-- parser outcome, never a separately assumed graph or certificate.
karpFractranDecodePreservesAcceptance :
  (word certificate : Word.BitWord) →
  nativeWholeWordAccepts word certificate
    ≡ Original.verifyFinFreeSparseGraphWord word certificate
karpFractranDecodePreservesAcceptance word certificate
  with Native.readNativeWholeRawGraphWord word in parsed
     | Fields.nativeOriginalGraphWordFieldsSame word
... | nothing | fields
  rewrite sym fields = refl
... | just (Native.native-parsed-raw-graph n paired thresholdLE) | fields
  with nativeWholeSuccessContainsActualEdgeReceipt
    word (Native.native-parsed-raw-graph n paired thresholdLE) parsed
... | m , (afterM , (afterEdges , receipt))
  rewrite sym fields =
  Accepted.karpNativeParsedRawAcceptanceSameOriginal
    m afterM paired afterEdges certificate thresholdLE receipt
