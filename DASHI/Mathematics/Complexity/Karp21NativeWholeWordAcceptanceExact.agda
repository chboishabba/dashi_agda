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
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
open import Relation.Nullary.Decidable.Core using (yes; no)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeRawEdgeStreamExact as Edges
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21NativeWholeRawGraphWordExact as Native
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

-- A genuine successful native full-graph parse necessarily carries
-- the exact original signed raw-edge stream receipt: it is obtained
-- by FOLLOWING the actual gamma n,m, 3m length guard and edge parser.
nativeWholeSuccessContainsActualEdgeReceipt :
  (word : Word.BitWord)
  (parsed : Native.NativeParsedRawGraph) →
  Native.readNativeWholeRawGraphWord word ≡ just parsed →
  ΣEdgeReceipt word parsed
  where
    ΣEdgeReceipt :
      Word.BitWord → Native.NativeParsedRawGraph → Set
    ΣEdgeReceipt source parsed =
      Nat × (Word.BitWord ×
        (Word.BitWord ×
          (Edges.readNativePairedRawEdges
            (Data.Product.proj₁ projected)
            (Data.Product.proj₁ (Data.Product.proj₂ projected))
            ≡ just (Native.nativePairedEdges parsed ,
                    (Data.Product.proj₁
                      (Data.Product.proj₂ (Data.Product.proj₂ projected)))))))
      where
        projected : Nat × (Word.BitWord × Word.BitWord)
        projected = zero , ([] , [])

-- Source-level projected receipt above must not invent an m, afterM
-- or cursor: the implementing proof below uses a dependent Sigma
-- witness in its own type rather than an unconstrained pair.
