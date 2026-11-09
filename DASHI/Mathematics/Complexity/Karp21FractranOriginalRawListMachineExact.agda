module DASHI.Mathematics.Complexity.Karp21FractranOriginalRawListMachineExact where

------------------------------------------------------------------------
-- P0-D: CONCRETE ORIGINAL N21 RAW-LIST FIRST-ENABLED MACHINE.
-- This is no longer just the earlier one-edge specialization:
--
-- state = complete remaining parsed ORIGINAL raw-edge/token list,
--         remaining ORIGINAL 2m certificate bits,
--         original chronological endpoint history,
--         actual native TWO-LANE signed binary ledger,
--         live/finished/rejected phase.
--
-- Priority advances a valid source edge; then accepts exactly when
-- both cursors are exhausted; otherwise rejects a malformed original
-- certificate or endpoint conflict. Halted states enable NO rule.
--
-- Source rawSparseScore and endpointConsistent are preserved; this
-- machine is NOT the terminal original graph-word decision since
-- positive threshold comparison after score traversal is OPEN.
-- No fabricated FRACTRAN prime factor or oracle premise is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original
import DASHI.Mathematics.Complexity.Karp21FractranPairedBinaryTraceExact as Paired
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21FractranPriorityFrontierExact as Frontier

data Phase : Set where
  active finished rejected : Phase

data Rule : Set where
  advance finish reject : Rule

record State : Set where
  constructor state
  field
    phase : Phase
    remainingEdges : List Paired.PairedRawEdge
    remainingCertificate : Word.BitWord
    endpointHistory : List (Nat × Bool)
    binaryLedger : Ledger.SignedLedger
open State public

sourceGuard : Rule → State → Bool
sourceGuard advance
  (state active
    ((Graph.raw-edge u v w , token) ∷ rest)
    (a ∷ b ∷ bits) history ledger) =
  Boolean.andBool
    (Original.endpointConsistent u a history)
    (Original.endpointConsistent v b history)
sourceGuard advance other = false
sourceGuard finish (state active [] [] history ledger) = true
sourceGuard finish other = false
sourceGuard reject (state active edges bits history ledger) = true
sourceGuard reject other = false

-- Exactly the original signed cut contribution selection:
-- when two original endpoint label bits agree, insert NO token.
addSelectedToken :
  Bool → Bool → Paired.PairedRawEdge →
  Ledger.SignedLedger → Ledger.SignedLedger
addSelectedToken a b (edge , token) ledger
  with Boolean.boolEqual a b
... | true = ledger
... | false = Ledger.insertSigned token ledger

applyRule : Rule → State → State
applyRule advance
  (state active
    ((Graph.raw-edge u v w , token) ∷ rest)
    (a ∷ b ∷ bits) history ledger) =
  state active rest bits
    ((u , a) ∷ (v , b) ∷ history)
    (addSelectedToken a b (Graph.raw-edge u v w , token) ledger)
applyRule advance s = s
applyRule finish (state active [] [] history ledger) =
  state finished [] [] history ledger
applyRule finish s = s
applyRule reject (state active edges bits history ledger) =
  state rejected edges bits history ledger
applyRule reject s = s

-- Conservative source-selective cache: all guards are invalidated.
-- Proving a sharper affected predicate is optional optimization and
-- cannot alter first-enabled priority/semantics.
affected : Rule → State → State → Bool
affected rule before after = true

unaffectedStable :
  ∀ rule before after →
  affected rule before after ≡ false →
  sourceGuard rule before ≡ sourceGuard rule after
unaffectedStable rule before after ()

module OriginalMachine =
  Frontier.Machine State Rule
    sourceGuard applyRule affected unaffectedStable

rules : List Rule
rules = advance ∷ finish ∷ reject ∷ []

-- Independent direct ORIGINAL N21 raw-list state step, NOT defined
-- by calling sourceGuard or Frontier.firstEnabled. The chronological
-- endpoint-history/certificate checks mirror original rawSparseScore.
originalRawListOneStep : State → Maybe State
originalRawListOneStep (state finished edges bits history ledger) =
  nothing
originalRawListOneStep (state rejected edges bits history ledger) =
  nothing
originalRawListOneStep (state active [] [] history ledger) =
  just (state finished [] [] history ledger)
originalRawListOneStep (state active [] (bit ∷ bits) history ledger) =
  just (state rejected [] (bit ∷ bits) history ledger)
originalRawListOneStep (state active (edge ∷ rest) [] history ledger) =
  just (state rejected (edge ∷ rest) [] history ledger)
originalRawListOneStep
  (state active (edge ∷ rest) (a ∷ []) history ledger) =
  just (state rejected (edge ∷ rest) (a ∷ []) history ledger)
originalRawListOneStep
  (state active
    ((Graph.raw-edge u v w , token) ∷ rest)
    (a ∷ b ∷ bits) history ledger)
  with Original.endpointConsistent u a history
     | Original.endpointConsistent v b history
... | false | _ =
  just (state rejected
    ((Graph.raw-edge u v w , token) ∷ rest)
    (a ∷ b ∷ bits) history ledger)
... | true | false =
  just (state rejected
    ((Graph.raw-edge u v w , token) ∷ rest)
    (a ∷ b ∷ bits) history ledger)
... | true | true =
  just (state active rest bits
    ((u , a) ∷ (v , b) ∷ history)
    (addSelectedToken a b (Graph.raw-edge u v w , token) ledger))

-- FULL ORIGINAL RAW-EDGE CURSOR *ONE-STEP* correspondence, including
-- terminal halt, completed cursor, overlong/short certificate and
-- original endpoint conflict. Does not conflate this with the full
-- graph decoder or terminal threshold decision.
karpFractranFirstEnabledSameRawCursorStep :
  (s : State) →
  OriginalMachine.directStep rules s ≡ originalRawListOneStep s
karpFractranFirstEnabledSameRawCursorStep
  (state finished edges bits history ledger) = refl
karpFractranFirstEnabledSameRawCursorStep
  (state rejected edges bits history ledger) = refl
karpFractranFirstEnabledSameRawCursorStep
  (state active [] [] history ledger) = refl
karpFractranFirstEnabledSameRawCursorStep
  (state active [] (bit ∷ bits) history ledger) = refl
karpFractranFirstEnabledSameRawCursorStep
  (state active (edge ∷ rest) [] history ledger) = refl
karpFractranFirstEnabledSameRawCursorStep
  (state active (edge ∷ rest) (a ∷ []) history ledger) = refl
karpFractranFirstEnabledSameRawCursorStep
  (state active
    ((Graph.raw-edge u v w , token) ∷ rest)
    (a ∷ b ∷ bits) history ledger)
  with Original.endpointConsistent u a history
     | Original.endpointConsistent v b history
... | false | _ = refl
... | true | false = refl
... | true | true = refl

-- Cache can never falsify the raw-cursor result: the concrete
-- predicate above invalidates all guards, an intentionally costly
-- baseline that is independent of any unproved locality assumption.
karpRawCursorCachedSameOriginalStep :
  (s : State) →
  OriginalMachine.cachedStep
    (OriginalMachine.populate rules s) s
    ≡ originalRawListOneStep s
karpRawCursorCachedSameOriginalStep s =
  Relation.Binary.PropositionalEquality.trans
    (OriginalMachine.cachedStepCorrect
      rules (OriginalMachine.populate rules s) s s refl)
    (karpFractranFirstEnabledSameRawCursorStep s)
