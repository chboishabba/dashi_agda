module DASHI.Mathematics.Complexity.Karp21FractranParsedRawThresholdMachineExact where

------------------------------------------------------------------------
-- P0-D/E: original N21 parsed raw-list FRACTRAN machine WITH actual
-- bit-native positive-threshold decision at cursor exhaustion.
--
-- Reuse the complete source raw-list machine, original
-- endpointConsistent/2-bit label checks, native signed ledger, and
-- actual Positive.meetsOriginalPositiveThreshold binary comparator.
--
-- Priority = advance, accept-if-threshold, reject. No match at all
-- when the machine is already finished/rejected (true halt).
-- Reference step is defined independently from the machine guards.
--
-- This does not replace the original graph-word decoder. The original
-- gamma n,m, validated Fin endpoints/strict edge order and positive
-- threshold cursor have yet to be welded into an all-word theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original
import DASHI.Mathematics.Complexity.Karp21FractranPairedBinaryTraceExact as Paired
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21FractranOriginalRawListMachineExact as Cursor
import DASHI.Mathematics.Complexity.Karp21FractranPriorityFrontierExact as Frontier

-- Threshold bits are fixed by the source graph gamma parser and are
-- little-endian. No unary Nat threshold executes in this machine.
module ParsedThresholdMachine (thresholdLE : Word.BitWord) where

  enabled : Cursor.Rule → Cursor.State → Bool
  enabled Cursor.advance state =
    Cursor.sourceGuard Cursor.advance state
  enabled Cursor.finish
    (Cursor.state Cursor.active [] [] history ledger) =
    Positive.meetsOriginalPositiveThreshold ledger thresholdLE
  enabled Cursor.finish state = false
  enabled Cursor.reject state =
    Cursor.sourceGuard Cursor.reject state

  apply : Cursor.Rule → Cursor.State → Cursor.State
  apply = Cursor.applyRule

  -- Conservative frontier: no invalid reuse of guards after a new
  -- certificate bit, ledger register or endpoint-history transition.
  affected : Cursor.Rule → Cursor.State → Cursor.State → Bool
  affected rule before after = true

  unaffectedStable :
    ∀ rule before after →
    affected rule before after ≡ false →
    enabled rule before ≡ enabled rule after
  unaffectedStable rule before after ()

  module Compiled =
    Frontier.Machine Cursor.State Cursor.Rule
      enabled apply affected unaffectedStable

  rules : List Cursor.Rule
  rules = Cursor.advance ∷ Cursor.finish ∷ Cursor.reject ∷ []

  -- The reference is not defined from firstEnabled or enabled: it
  -- independently branches on the actual remaining source grammar,
  -- then invokes the original raw-list one-step in non-final states.
  originalParsedRawVerifierStep :
    Cursor.State → Maybe Cursor.State
  originalParsedRawVerifierStep
    (Cursor.state Cursor.active [] [] history ledger)
    with Positive.meetsOriginalPositiveThreshold ledger thresholdLE
  ... | true =
    just (Cursor.state Cursor.finished [] [] history ledger)
  ... | false =
    just (Cursor.state Cursor.rejected [] [] history ledger)
  originalParsedRawVerifierStep state =
    Cursor.originalRawListOneStep state

  -- The COMPLETE parsed signed raw-edge and certificate cursor,
  -- including native terminal POSITIVE threshold decision. This is
  -- strictly stronger than the preceding score-only cursor theorem.
  karpFractranFirstEnabledSameParsedRawVerifierStep :
    (s : Cursor.State) →
    Compiled.directStep rules s ≡ originalParsedRawVerifierStep s
  karpFractranFirstEnabledSameParsedRawVerifierStep
    (Cursor.state Cursor.active [] [] history ledger)
    with Positive.meetsOriginalPositiveThreshold ledger thresholdLE
  ... | true = refl
  ... | false = refl
  karpFractranFirstEnabledSameParsedRawVerifierStep
    (Cursor.state Cursor.finished edges bits history ledger) = refl
  karpFractranFirstEnabledSameParsedRawVerifierStep
    (Cursor.state Cursor.rejected edges bits history ledger) = refl
  karpFractranFirstEnabledSameParsedRawVerifierStep
    (Cursor.state Cursor.active [] (a ∷ bits) history ledger) = refl
  karpFractranFirstEnabledSameParsedRawVerifierStep
    (Cursor.state Cursor.active (edge ∷ rest) [] history ledger) = refl
  karpFractranFirstEnabledSameParsedRawVerifierStep
    (Cursor.state Cursor.active (edge ∷ rest) (a ∷ []) history ledger) = refl
  karpFractranFirstEnabledSameParsedRawVerifierStep
    (Cursor.state Cursor.active
      ((Graph.raw-edge u v w , token) ∷ rest)
      (a ∷ b ∷ bits) history ledger)
    with Original.endpointConsistent u a history
       | Original.endpointConsistent v b history
  ... | false | _ = refl
  ... | true | false = refl
  ... | true | true = refl

  -- The generic incremental priority certificate still applies:
  -- a refreshed cache yields exactly the same original parsed
  -- threshold step. We do NOT assert a cache-speedup.
  karpParsedRawCachedSameOriginalStep :
    (s : Cursor.State) →
    Compiled.cachedStep
      (Compiled.refreshCache (Compiled.populate rules s) s s) s
      ≡ originalParsedRawVerifierStep s
  karpParsedRawCachedSameOriginalStep s =
    trans
      (Compiled.cachedStepCorrect
        rules (Compiled.populate rules s) s s refl)
      (karpFractranFirstEnabledSameParsedRawVerifierStep s)
