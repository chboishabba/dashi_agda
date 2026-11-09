module DASHI.Mathematics.Complexity.Karp21NativeWholeBinarySelectedEventTraceExact where

------------------------------------------------------------------------
-- E1: EMITTED selected signed-gamma events from the ACTUAL ordered
-- first-enabled BINARY N21 source machine.
--
-- This follows Machine.Compiled.directStep, not a separately supplied
-- selected token list or a numerical weight oracle. A valid sparse
-- witness emits one signed binary token iff its endpoint labels differ.
-- Terminal threshold rejection is deliberately NOT confused with a
-- malformed witness: the selected-edge trace still exists even when
-- total signed score is below W. Malformed certificates reject trace.
--
-- Original source signed-value observation is only proof-side.
-- Kernel checking, actual typed machine trace and tape cost are
-- independent exact-head obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.List.Base using (length)
open import Data.Product using (_×_; _,_)
open import Data.Integer.Base using (ℤ)
open import Relation.Binary.PropositionalEquality using (cong; sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeOriginalValueExact as Weight
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact as History
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryOriginalExact as HistoryOriginal
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryPriorityMachineExact as Machine
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FractranOriginalRawTraceReplayExact as Original

-- The first-enabled machine is the executed transition engine.
-- Finite fuel is the SAME source edge-count+1 bound. The event
-- register records selection but does not construct original ℤ.
actualFirstEnabledSelectedEvents :
  Nat → Machine.State → Maybe (List Signed.SignedMagnitudeBits)
actualFirstEnabledSelectedEvents zero state = nothing
actualFirstEnabledSelectedEvents (suc fuel)
  (Machine.state Machine.active [] [] history ledger threshold) =
  just []
actualFirstEnabledSelectedEvents (suc fuel)
  (Machine.state Machine.active
    (Edge.binary-edge u v token ∷ rest)
    (a ∷ b ∷ bits) history ledger threshold)
  with Machine.Compiled.directStep Machine.rules
    (Machine.state Machine.active
      (Edge.binary-edge u v token ∷ rest)
      (a ∷ b ∷ bits) history ledger threshold)
... | nothing = nothing
... | just next
  with Machine.phase next
... | Machine.rejected = nothing
... | Machine.accepted = nothing
... | Machine.active with
    actualFirstEnabledSelectedEvents fuel next
... | nothing = nothing
... | just selected with Boolean.boolEqual a b
... | true = just selected
... | false = just (token ∷ selected)
actualFirstEnabledSelectedEvents (suc fuel) other = nothing

observeSignedEvents : List Signed.SignedMagnitudeBits → List ℤ
observeSignedEvents [] = []
observeSignedEvents (token ∷ rest) =
  Weight.interpretNativeToken token ∷ observeSignedEvents rest

observeMaybeSignedEvents :
  Maybe (List Signed.SignedMagnitudeBits) → Maybe (List ℤ)
observeMaybeSignedEvents nothing = nothing
observeMaybeSignedEvents (just tokens) =
  just (observeSignedEvents tokens)

-- The original raw signed-edge trace is a right-ordered selection
-- built by EXACT original endpointConsistent and boolEqual rules.
-- The event run uses ACTUAL binary next-step state and its recorder.
nativeFirstEnabledSelectedEventsSameOriginal :
  (edges : List Edge.BinaryRawEdge)
  (certificate : Word.BitWord)
  (history : History.BinaryEndpointHistory)
  (ledger : Ledger.SignedLedger)
  (threshold : Word.BitWord) →
  observeMaybeSignedEvents
    (actualFirstEnabledSelectedEvents (suc (length edges))
      (Machine.state Machine.active edges certificate
        history ledger threshold))
  ≡ Original.rawSelectedTrace
      (Edge.originalEdgeListObservation edges)
      certificate (History.observedBinaryHistory history)
nativeFirstEnabledSelectedEventsSameOriginal [] [] history ledger threshold = refl
nativeFirstEnabledSelectedEventsSameOriginal [] (_ ∷ _) history ledger threshold = refl
nativeFirstEnabledSelectedEventsSameOriginal (_ ∷ _) [] history ledger threshold = refl
nativeFirstEnabledSelectedEventsSameOriginal (_ ∷ _) (_ ∷ []) history ledger threshold = refl
nativeFirstEnabledSelectedEventsSameOriginal
  (Edge.binary-edge u v token ∷ rest)
  (a ∷ b ∷ bits) history ledger threshold
  with History.endpointConsistentBinary u a history
     | History.endpointConsistentBinary v b history
     | HistoryOriginal.nativeBinaryEndpointHistorySameOriginal
         u a history
     | HistoryOriginal.nativeBinaryEndpointHistorySameOriginal
         v b history
... | false | _ | uEq | vEq
  rewrite sym uEq | sym vEq = refl
... | true | false | uEq | vEq
  rewrite sym uEq | sym vEq = refl
... | true | true | uEq | vEq
  rewrite sym uEq | sym vEq
  with Boolean.boolEqual a b
... | same
  with actualFirstEnabledSelectedEvents (suc (length rest))
    (Machine.state Machine.active rest bits
      (History.recordBinaryEndpointPair u v a b history)
      (Machine.addSelectedBinaryToken a b
        (Edge.binary-edge u v token) ledger)
      threshold)
     | nativeFirstEnabledSelectedEventsSameOriginal
         rest bits
         (History.recordBinaryEndpointPair u v a b history)
         (Machine.addSelectedBinaryToken a b
           (Edge.binary-edge u v token) ledger)
         threshold
... | nothing | tailEq
  rewrite sym tailEq = refl
... | just selected | tailEq
  rewrite sym tailEq
  with same
... | true = refl
... | false = refl
