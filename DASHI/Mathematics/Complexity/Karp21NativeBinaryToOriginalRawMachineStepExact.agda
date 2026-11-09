module DASHI.Mathematics.Complexity.Karp21NativeBinaryToOriginalRawMachineStepExact where

------------------------------------------------------------------------
-- D2 actual cross-machine simulation, NOT two independently named
-- binary source-reference steps. The OLD original N21 raw-list source
-- machine holds (original Graph.RawEdge, native SignedMagnitudeBits)
-- and ORIGINAL Nat endpoint-history; the NEW bit-native whole graph
-- machine holds LE binary u/v and the same signed gamma tokens.
--
-- The observation below transports binary endpoint values to the
-- EXACT original paired raw-edge and history state, proof-side only.
-- It proves all nonterminal cursor operations, malformed/short
-- certificates and endpoint conflicts, using the original NatP
-- endpoint-consistency theorem, not an assumed same-step oracle.
--
-- TERMINAL EXCEPTION: original raw cursor always marks FINISHED and
-- binary whole graph checks positive W first. Use the independent
-- originalRawFinishedThresholdObservationSameBinaryTerminal theorem;
-- literal unconditional terminal phase equality is disproven by its
-- W=1 empty-ledger negative control.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21FractranPairedBinaryTraceExact as Paired
import DASHI.Mathematics.Complexity.Karp21FractranOriginalRawListMachineExact as Raw
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryPriorityMachineExact as Binary
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact as History
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryOriginalExact as HistoryOriginal
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger

observeBinaryPairedEdges :
  List Edge.BinaryRawEdge → List Paired.PairedRawEdge
observeBinaryPairedEdges [] = []
observeBinaryPairedEdges (Edge.binary-edge u v token ∷ rest) =
  (Edge.originalEdgeObservation (Edge.binary-edge u v token) , token)
    ∷ observeBinaryPairedEdges rest

observeBinaryPhase : Binary.Phase → Raw.Phase
observeBinaryPhase Binary.active = Raw.active
observeBinaryPhase Binary.accepted = Raw.finished
observeBinaryPhase Binary.rejected = Raw.rejected

observeBinaryRawState : Binary.State → Raw.State
observeBinaryRawState (Binary.state phase edges bits history ledger threshold) =
  Raw.state (observeBinaryPhase phase)
    (observeBinaryPairedEdges edges)
    bits (History.observedBinaryHistory history) ledger

observeMaybeBinaryRawState : Maybe Binary.State → Maybe Raw.State
observeMaybeBinaryRawState nothing = nothing
observeMaybeBinaryRawState (just state) =
  just (observeBinaryRawState state)

-- Both machines truly HALT, regardless of their stored terminal data.
binaryAcceptedHaltSameOriginalFinished :
  (edges : List Edge.BinaryRawEdge)
  (bits : Word.BitWord)
  (history : History.BinaryEndpointHistory)
  (ledger : Ledger.SignedLedger)
  (threshold : Word.BitWord) →
  observeMaybeBinaryRawState
    (Binary.originalBinaryWholeVerifierStep
      (Binary.state Binary.accepted edges bits history ledger threshold))
  ≡ Raw.originalRawListOneStep
      (observeBinaryRawState
        (Binary.state Binary.accepted edges bits history ledger threshold))
binaryAcceptedHaltSameOriginalFinished edges bits history ledger threshold =
  refl

binaryRejectedHaltSameOriginalRejected :
  (edges : List Edge.BinaryRawEdge)
  (bits : Word.BitWord)
  (history : History.BinaryEndpointHistory)
  (ledger : Ledger.SignedLedger)
  (threshold : Word.BitWord) →
  observeMaybeBinaryRawState
    (Binary.originalBinaryWholeVerifierStep
      (Binary.state Binary.rejected edges bits history ledger threshold))
  ≡ Raw.originalRawListOneStep
      (observeBinaryRawState
        (Binary.state Binary.rejected edges bits history ledger threshold))
binaryRejectedHaltSameOriginalRejected edges bits history ledger threshold =
  refl

-- The original extra-certificate rule is identical on the same
-- actual source cursor (the positive threshold is not yet inspected).
binaryExtraCertificateRejectsSameOriginal :
  (a : Bool) (bits : Word.BitWord)
  (history : History.BinaryEndpointHistory)
  (ledger : Ledger.SignedLedger)
  (threshold : Word.BitWord) →
  observeMaybeBinaryRawState
    (Binary.originalBinaryWholeVerifierStep
      (Binary.state Binary.active [] (a ∷ bits) history ledger threshold))
  ≡ Raw.originalRawListOneStep
      (observeBinaryRawState
        (Binary.state Binary.active [] (a ∷ bits) history ledger threshold))
binaryExtraCertificateRejectsSameOriginal a bits history ledger threshold =
  refl

-- All nonempty remaining-original-raw-edge cursors, even with empty,
-- one-bit, conflicting or otherwise malformed sparse certificates.
nativeBinaryFirstEnabledNonterminalSameOriginalRawStep :
  (edge : Edge.BinaryRawEdge)
  (rest : List Edge.BinaryRawEdge)
  (bits : Word.BitWord)
  (history : History.BinaryEndpointHistory)
  (ledger : Ledger.SignedLedger)
  (threshold : Word.BitWord) →
  observeMaybeBinaryRawState
    (Binary.originalBinaryWholeVerifierStep
      (Binary.state Binary.active (edge ∷ rest)
        bits history ledger threshold))
  ≡ Raw.originalRawListOneStep
      (observeBinaryRawState
        (Binary.state Binary.active (edge ∷ rest)
          bits history ledger threshold))
nativeBinaryFirstEnabledNonterminalSameOriginalRawStep
  edge rest [] history ledger threshold = refl
nativeBinaryFirstEnabledNonterminalSameOriginalRawStep
  edge rest (a ∷ []) history ledger threshold = refl
nativeBinaryFirstEnabledNonterminalSameOriginalRawStep
  (Edge.binary-edge u v token) rest (a ∷ b ∷ bits)
  history ledger threshold
  with History.endpointConsistentBinary u a history
     | History.endpointConsistentBinary v b history
     | HistoryOriginal.nativeBinaryEndpointHistorySameOriginal u a history
     | HistoryOriginal.nativeBinaryEndpointHistorySameOriginal v b history
... | false | _ | eqU | eqV
  rewrite sym eqU | sym eqV = refl
... | true | false | eqU | eqV
  rewrite sym eqU | sym eqV = refl
... | true | true | eqU | eqV
  rewrite sym eqU | sym eqV
  with Boolean.boolEqual a b
... | true = refl
... | false = refl

-- This D2 lemma is a genuine ORIGINAL raw-list step correspondence,
-- not a comparison to another freshly defined binary reference step.
-- Compose its one-to-one nonterminal simulation with the threshold
-- terminal quotient and the B6 signed event-trace theorem.
