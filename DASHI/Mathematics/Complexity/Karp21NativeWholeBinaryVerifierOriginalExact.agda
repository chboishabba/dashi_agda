module DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryVerifierOriginalExact where

------------------------------------------------------------------------
-- B6 terminal SAME ORIGINAL FIN-FREE signed N21 verifier theorem.
--
-- Left side runs the REAL executable binary graph word reader:
-- gamma n/m/u/v bit registers, actual m budget and input fuel,
-- strict canonical binary edge validation, strictly positive gamma W,
-- actual endpoint-history consistency, two-lane signed ripple ledger,
-- and bitwise positive threshold comparator.
--
-- Right side is LITERALLY Original.verifyFinFreeSparseGraphWord.
-- Proof-side observers use Nat/ℤ solely to establish equality.
--
-- IMPORTANT: Agda kernel acceptance and the original TYPED Fin/Cut
-- verifier transport are independent unpaid gates. No polynomial
-- bit-Turing-machine clock or PR.InNP is concluded here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Integer.Base as Int
import Data.Integer.Properties as IntP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Graph
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphOriginalExact as GraphOriginal
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryVerifierExact as Machine
import DASHI.Mathematics.Complexity.Karp21NativeBinaryCutLedgerOriginalExact as Cut
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact as History
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21NativeLedgerIntegerScoreExact as Score
import DASHI.Mathematics.Complexity.Karp21NativeThresholdOriginalSignedDecisionExact as Threshold
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original

-- The arbitrary-initial-ledger correspondence from the actual binary
-- cursor simplifies exactly at its canonical empty runtime register.
emptyInitialLedgerScore :
  (result : Maybe Int.ℤ) →
  Cut.originalScoreWithInitialLedger Ledger.emptyLedger result ≡ result
emptyInitialLedgerScore nothing = refl
emptyInitialLedgerScore (just score) =
  cong just (IntP.+-identityˡ score)

-- No separately supplied matching score, no fabricated original
-- proof premise: the actual binary cursor determines the RHS itself.
binaryCutLedgerSameOriginalAtEmpty :
  (edges : Agda.Builtin.List.List Edge.BinaryRawEdge)
  (certificate : Word.BitWord) →
  Cut.observedBinaryLedgerRun
    (Machine.readNativeBinaryCutLedger edges certificate []
      Ledger.emptyLedger)
  ≡ Original.rawSparseScore
      (Edge.originalEdgeListObservation edges) certificate []
binaryCutLedgerSameOriginalAtEmpty edges certificate =
  trans
    (Cut.nativeBinaryCutLedgerSameOriginal
      edges certificate [] Ledger.emptyLedger)
    (emptyInitialLedgerScore
      (Original.rawSparseScore
        (Edge.originalEdgeListObservation edges) certificate []))

-- SAME INPUT graph and certificate words, including every original
-- malformed parser/validator/certificate branch, signed threshold,
-- and sparse endpoint conflict.
nativeWholeBinaryVerifierSameOriginalFinFree :
  (word certificate : Word.BitWord) →
  Machine.verifyNativeWholeBinaryGraphWord word certificate
    ≡ Original.verifyFinFreeSparseGraphWord word certificate
nativeWholeBinaryVerifierSameOriginalFinFree word certificate
  with Graph.readNativeWholeBinaryGraphWord word in graphParse
     | GraphOriginal.nativeWholeBinaryGraphWordSameOriginal word
... | nothing | graphEq rewrite sym graphEq = refl
... | just (Graph.whole-binary-graph n edges thresholdLE) | graphEq
  rewrite sym graphEq
  with Machine.readNativeBinaryCutLedger
         edges certificate [] Ledger.emptyLedger
     | binaryCutLedgerSameOriginalAtEmpty edges certificate
... | nothing | scoreEq rewrite sym scoreEq = refl
... | just ledger | scoreEq
  rewrite sym scoreEq =
  Threshold.karpNativeThresholdDecisionSameOriginal ledger thresholdLE
