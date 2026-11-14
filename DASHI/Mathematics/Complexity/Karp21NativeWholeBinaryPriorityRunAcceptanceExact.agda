module DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryPriorityRunAcceptanceExact where

------------------------------------------------------------------------
-- D2/E1 REAL ORIGINAL-WIRE BINARY FIRST-ENABLED RUN READOUT.
--
-- The genuinely ordered binary source machine's finite first-enabled
-- run (advance, finish, reject) has the EXACT SAME decision as the
-- existing independent recursive executable binary N21 verifier.
-- This works for arbitrary original wire graph word/certificate and
-- all raw cursor/history/ledger states, not merely a single example.
--
-- Note: source trace LIST equality and physical bit-TM clock remain
-- independent; this is complete terminal acceptance readout only.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact as History
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Graph
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryVerifierExact as Recursive
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryPriorityMachineExact as Machine
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryFiniteRunExact as Run
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryStepPotentialExact as Potential
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryTypedAcceptanceExact as Typed
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Original

-- Only the terminal accepted phase is accepting; inactive and
-- rejected states NEVER count as successful by default.
acceptedBinaryState : Machine.State → Bool
acceptedBinaryState
  (Machine.state Machine.accepted es bits hist ledger threshold) = true
acceptedBinaryState other = false

recursiveBinaryCursorDecision :
  List Edge.BinaryRawEdge → Word.BitWord →
  History.BinaryEndpointHistory → Ledger.SignedLedger →
  Word.BitWord → Bool
recursiveBinaryCursorDecision edges cert history ledger threshold
  with Recursive.readNativeBinaryCutLedger edges cert history ledger
... | nothing = false
... | just result =
  Positive.meetsOriginalPositiveThreshold result threshold

-- The ACTUAL compiled machine's initial-edge-count+1 run reproduces
-- the independent recursively evaluated real binary ledger and
-- terminal threshold, for arbitrary starting ledger and history.
binaryFirstEnabledRunMatchesRecursiveCursor :
  (edges : List Edge.BinaryRawEdge)
  (cert : Word.BitWord)
  (history : History.BinaryEndpointHistory)
  (ledger : Ledger.SignedLedger)
  (threshold : Word.BitWord) →
  acceptedBinaryState
    (Run.runBinaryWithFuel (suc (length edges))
      (Machine.state Machine.active edges cert history ledger threshold))
    ≡ recursiveBinaryCursorDecision edges cert history ledger threshold
binaryFirstEnabledRunMatchesRecursiveCursor [] [] history ledger threshold
  with Positive.meetsOriginalPositiveThreshold ledger threshold
... | true = refl
... | false = refl
binaryFirstEnabledRunMatchesRecursiveCursor [] (_ ∷ _) history ledger threshold =
  refl
binaryFirstEnabledRunMatchesRecursiveCursor (_ ∷ _) [] history ledger threshold =
  refl
binaryFirstEnabledRunMatchesRecursiveCursor (_ ∷ _) (_ ∷ []) history ledger threshold =
  refl
binaryFirstEnabledRunMatchesRecursiveCursor
  (Edge.binary-edge u v token ∷ rest)
  (a ∷ b ∷ bits) history ledger threshold
  with History.endpointConsistentBinary u a history
     | History.endpointConsistentBinary v b history
... | false | _ = refl
... | true | false = refl
... | true | true
  with Boolean.boolEqual a b
... | true =
  binaryFirstEnabledRunMatchesRecursiveCursor
    rest bits (History.recordBinaryEndpointPair u v a b history)
    ledger threshold
... | false =
  binaryFirstEnabledRunMatchesRecursiveCursor
    rest bits (History.recordBinaryEndpointPair u v a b history)
    (Ledger.insertSigned token ledger) threshold

-- Malformed whole binary graph input initializes a halted rejected
-- state, whereas valid graph input initializes the identical ordered
-- binary edge cursor and signed ledger/threshold.
binaryWholeWordFirstEnabledRunMatchesExecutableVerifier :
  (word certificate : Word.BitWord) →
  acceptedBinaryState
    (Run.runBinaryWithFuel
      (Potential.binaryStatePotential
        (Machine.initialBinaryWholeWordState word certificate))
      (Machine.initialBinaryWholeWordState word certificate))
    ≡ Recursive.verifyNativeWholeBinaryGraphWord word certificate
binaryWholeWordFirstEnabledRunMatchesExecutableVerifier word certificate
  with Graph.readNativeWholeBinaryGraphWord word
... | nothing = refl
... | just (Graph.whole-binary-graph n edges threshold) =
  binaryFirstEnabledRunMatchesRecursiveCursor
    edges certificate [] Ledger.emptyLedger threshold

-- E2/semantic original typed N21 readout of the SAME actual
-- first-enabled run. No distinct graph/certificate grammar, no oracle.
binaryFirstEnabledRunSameOriginalTypedN21 :
  (word certificate : Word.BitWord) →
  acceptedBinaryState
    (Run.runBinaryWithFuel
      (Potential.binaryStatePotential
        (Machine.initialBinaryWholeWordState word certificate))
      (Machine.initialBinaryWholeWordState word certificate))
    ≡ Original.LiteralN21.verifyCanonicalSparseGraphWord
         word certificate
binaryFirstEnabledRunSameOriginalTypedN21 word certificate =
  trans
    (binaryWholeWordFirstEnabledRunMatchesExecutableVerifier
      word certificate)
    (Typed.nativeCanonicalTypedSparseVerifierSameWord
      word certificate)
