module DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryPriorityMachineExact where

------------------------------------------------------------------------
-- D1/D2 CONCRETE ORIGINAL-WIRE N21 BINARY FIRST-ENABLED MACHINE.
-- The state starts from the REAL bit-native graph parser. A cursor
-- step consumes the exact original two certificate bits, checks
-- chronological bit-native endpoint identity and applies signed
-- two-lane ripple ledger contribution. Terminal step checks the real
-- positive binary threshold. Malformed word/certificate reject;
-- accepted/rejected states genuinely HALT (no rule enabled).
--
-- This owner is NOT a replacement for the cross-observation theorem
-- to the original typed Fin/Cut machine or a physical bit-TM clock.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact as History
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Graph
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphOriginalExact as OriginalGraph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original
import DASHI.Mathematics.Complexity.Karp21FractranPriorityFrontierExact as Frontier

data Phase : Set where
  active accepted rejected : Phase

data Rule : Set where
  advance finish reject : Rule

record State : Set where
  constructor state
  field
    phase : Phase
    edges : List Edge.BinaryRawEdge
    bits : Word.BitWord
    history : History.BinaryEndpointHistory
    ledger : Ledger.SignedLedger
    threshold : Word.BitWord
open State public

-- This is the concrete source execution state, not an abstract
-- initial-state oracle. A failed original graph-word parse is an
-- already-rejected, halted state.
initialBinaryWholeWordState : Word.BitWord → Word.BitWord → State
initialBinaryWholeWordState word certificate
  with Graph.readNativeWholeBinaryGraphWord word
... | nothing =
  state rejected [] [] [] Ledger.emptyLedger []
... | just (Graph.whole-binary-graph n edges w) =
  state active edges certificate [] Ledger.emptyLedger w

-- The following priority list is genuinely ordered; reject is the
-- fallback iff no legal advance/accept rule is enabled.
enabled : Rule → State → Bool
enabled advance
  (state active (Edge.binary-edge u v w ∷ rest)
    (a ∷ b ∷ bits) history ledger threshold) =
  Boolean.andBool
    (History.endpointConsistentBinary u a history)
    (History.endpointConsistentBinary v b history)
enabled advance other = false
enabled finish (state active [] [] history ledger threshold) =
  Positive.meetsOriginalPositiveThreshold ledger threshold
enabled finish other = false
enabled reject (state active edges bits history ledger threshold) =
  true
enabled reject other = false

-- Actual original certificate selection: equal labels add NO weight;
-- unequal labels add the genuine signed binary token.
addSelectedBinaryToken :
  Bool → Bool → Edge.BinaryRawEdge →
  Ledger.SignedLedger → Ledger.SignedLedger
addSelectedBinaryToken a b (Edge.binary-edge u v token) ledger
  with Boolean.boolEqual a b
... | true = ledger
... | false = Ledger.insertSigned token ledger

apply : Rule → State → State
apply advance
  (state active (Edge.binary-edge u v token ∷ rest)
    (a ∷ b ∷ bits) history ledger threshold) =
  state active rest bits
    (History.recordBinaryEndpointPair u v a b history)
    (addSelectedBinaryToken a b
      (Edge.binary-edge u v token) ledger)
    threshold
apply advance s = s
apply finish (state active [] [] history ledger threshold) =
  state accepted [] [] history ledger threshold
apply finish s = s
apply reject (state active edges bits history ledger threshold) =
  state rejected edges bits history ledger threshold
apply reject s = s

-- Conservative cache invalidation: no unproved locality speedup.
affected : Rule → State → State → Bool
affected rule before after = true

unaffectedStable :
  ∀ rule before after →
  affected rule before after ≡ false →
  enabled rule before ≡ enabled rule after
unaffectedStable rule before after ()

module Compiled =
  Frontier.Machine State Rule
    enabled apply affected unaffectedStable

rules : List Rule
rules = advance ∷ finish ∷ reject ∷ []

-- Independent source reference step (not implemented via enabled,
-- firstEnabled, directStep or a chosen operation oracle).
originalBinaryWholeVerifierStep : State → Maybe State
originalBinaryWholeVerifierStep
  (state accepted es bits hist ledger threshold) = nothing
originalBinaryWholeVerifierStep
  (state rejected es bits hist ledger threshold) = nothing
originalBinaryWholeVerifierStep
  (state active [] [] hist ledger threshold)
  with Positive.meetsOriginalPositiveThreshold ledger threshold
... | true = just (state accepted [] [] hist ledger threshold)
... | false = just (state rejected [] [] hist ledger threshold)
originalBinaryWholeVerifierStep
  (state active [] (a ∷ bits) hist ledger threshold) =
  just (state rejected [] (a ∷ bits) hist ledger threshold)
originalBinaryWholeVerifierStep
  (state active (edge ∷ rest) [] hist ledger threshold) =
  just (state rejected (edge ∷ rest) [] hist ledger threshold)
originalBinaryWholeVerifierStep
  (state active (edge ∷ rest) (a ∷ []) hist ledger threshold) =
  just (state rejected (edge ∷ rest) (a ∷ []) hist ledger threshold)
originalBinaryWholeVerifierStep
  (state active
    (Edge.binary-edge u v token ∷ rest)
    (a ∷ b ∷ bits) hist ledger threshold)
  with History.endpointConsistentBinary u a hist
     | History.endpointConsistentBinary v b hist
... | false | _ =
  just (state rejected
    (Edge.binary-edge u v token ∷ rest)
    (a ∷ b ∷ bits) hist ledger threshold)
... | true | false =
  just (state rejected
    (Edge.binary-edge u v token ∷ rest)
    (a ∷ b ∷ bits) hist ledger threshold)
... | true | true =
  just (state active rest bits
    (History.recordBinaryEndpointPair u v a b hist)
    (addSelectedBinaryToken a b (Edge.binary-edge u v token) ledger)
    threshold)

-- D2 actual compiled first-enabled versus independent reference,
-- all states, malformed input and certificate, and true halt.
karpNativeBinaryFirstEnabledSameVerifierStep :
  (s : State) →
  Compiled.directStep rules s ≡ originalBinaryWholeVerifierStep s
karpNativeBinaryFirstEnabledSameVerifierStep
  (state accepted es bits hist ledger threshold) = refl
karpNativeBinaryFirstEnabledSameVerifierStep
  (state rejected es bits hist ledger threshold) = refl
karpNativeBinaryFirstEnabledSameVerifierStep
  (state active [] [] hist ledger threshold)
  with Positive.meetsOriginalPositiveThreshold ledger threshold
... | true = refl
... | false = refl
karpNativeBinaryFirstEnabledSameVerifierStep
  (state active [] (a ∷ bits) hist ledger threshold) = refl
karpNativeBinaryFirstEnabledSameVerifierStep
  (state active (edge ∷ rest) [] hist ledger threshold) = refl
karpNativeBinaryFirstEnabledSameVerifierStep
  (state active (edge ∷ rest) (a ∷ []) hist ledger threshold) = refl
karpNativeBinaryFirstEnabledSameVerifierStep
  (state active (Edge.binary-edge u v token ∷ rest)
    (a ∷ b ∷ bits) hist ledger threshold)
  with History.endpointConsistentBinary u a hist
     | History.endpointConsistentBinary v b hist
... | false | _ = refl
... | true | false = refl
... | true | true = refl

karpNativeBinaryCachedSameVerifierStep :
  (s : State) →
  Compiled.cachedStep
    (Compiled.refreshCache (Compiled.populate rules s) s s) s
    ≡ originalBinaryWholeVerifierStep s
karpNativeBinaryCachedSameVerifierStep s =
  trans
    (Compiled.cachedStepCorrect
      rules (Compiled.populate rules s) s s refl)
    (karpNativeBinaryFirstEnabledSameVerifierStep s)

-- A failed actual binary whole-word graph parse halts as rejected;
-- B6 source parsing correspondence proves that this is EXACTLY a
-- source-original rejected graph word, not an invented rejection.
originalGraphRejectsWhenBinaryInitialRejected :
  (word certificate : Word.BitWord) →
  Graph.readNativeWholeBinaryGraphWord word ≡ nothing →
  Original.readRawGraphWord word ≡ nothing
originalGraphRejectsWhenBinaryInitialRejected word certificate failed
  with Graph.readNativeWholeBinaryGraphWord word
... | nothing =
  OriginalGraph.nativeWholeBinaryGraphWordSameOriginal word
... | just parsed with failed
... | ()
