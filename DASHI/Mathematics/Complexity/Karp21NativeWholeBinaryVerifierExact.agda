module DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryVerifierExact where

------------------------------------------------------------------------
-- ORIGINAL N21 SIGNED WEIGHTED MAX CUT: executable binary-only path.
--
-- This is an ACTUAL implemented verifier, not a conditional record:
--   source gamma n/m, strict 3m input budget,
--   source gamma u/v signed gamma weight, strict canonical edge order,
--   original 2-bits-per-edge sparse certificate, vertex label history,
--   signed bitwise two-lane ripple accumulator, positive threshold.
--
-- All potentially enormous decoded gamma numbers remain LE BITWORDS.
-- No Nat/Fin/ℤ value reconstruction runs on this verifier path.
-- Original Nat length of the finite input suffix is used only as
-- STRUCTURAL FUEL, never as the numerical value of gamma(n/m/u/v).
--
-- All-word correctness against the original typed verifier, actual
-- bit-TM head/tape/width/clock, PR.InNP and SATNotInP remain OPEN.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Graph
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact as History
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive

-- Same ORIGINAL chronological endpoint history, complete certificate
-- consumption and signed cut selection; no Nat vertex equality.
readNativeBinaryCutLedger :
  List Edge.BinaryRawEdge →
  Word.BitWord →
  History.BinaryEndpointHistory →
  Ledger.SignedLedger →
  Maybe Ledger.SignedLedger
readNativeBinaryCutLedger [] [] history ledger = just ledger
readNativeBinaryCutLedger [] (_ ∷ _) history ledger = nothing
readNativeBinaryCutLedger (_ ∷ _) [] history ledger = nothing
readNativeBinaryCutLedger (_ ∷ _) (_ ∷ []) history ledger = nothing
readNativeBinaryCutLedger
  (Edge.binary-edge u v signed ∷ rest)
  (a ∷ b ∷ bits) history ledger
  with History.endpointConsistentBinary u a history
     | History.endpointConsistentBinary v b history
... | false | _ = nothing
... | true | false = nothing
... | true | true with Boolean.boolEqual a b
... | true =
  readNativeBinaryCutLedger rest bits
    (History.recordBinaryEndpointPair u v a b history)
    ledger
... | false =
  readNativeBinaryCutLedger rest bits
    (History.recordBinaryEndpointPair u v a b history)
    (Ledger.insertSigned signed ledger)

-- TOTAL executable binary source program; no unary gamma decode.
verifyNativeWholeBinaryGraphWord :
  Word.BitWord → Word.BitWord → Bool
verifyNativeWholeBinaryGraphWord word certificate
  with Graph.readNativeWholeBinaryGraphWord word
... | nothing = false
... | just (Graph.whole-binary-graph n edges threshold)
  with readNativeBinaryCutLedger
    edges certificate [] Ledger.emptyLedger
... | nothing = false
... | just ledger =
  Positive.meetsOriginalPositiveThreshold ledger threshold
