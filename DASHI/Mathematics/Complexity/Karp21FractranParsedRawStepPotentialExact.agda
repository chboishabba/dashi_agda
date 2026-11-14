module DASHI.Mathematics.Complexity.Karp21FractranParsedRawStepPotentialExact where

------------------------------------------------------------------------
-- P0-F: SOURCE concrete N21 parsed-raw FRACDASH step potential.
--
-- Each enabled raw-list advance consumes exactly one ORIGINAL edge;
-- finished/rejected states halt; a terminal threshold decision costs
-- exactly one additional top-level transition. Thus the high-level
-- number of rule firings is bounded by original m+1 for the parsed
-- raw-edge machine, independent of signed integer magnitudes.
--
-- IMPORTANT: This is NOT a bit-Turing-machine polynomial clock.
-- Each rule may still execute source unary Nat parsing/endpoint
-- comparison, actual bit addition and tape operations. Those physical
-- costs and original input graph validation remain P0-F unpaid.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original
import DASHI.Mathematics.Complexity.Karp21FractranOriginalRawListMachineExact as Cursor
import DASHI.Mathematics.Complexity.Karp21FractranParsedRawThresholdMachineExact as Threshold
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive

-- Potential zero is reserved for ACTUAL halted states.
cursorPotential : Cursor.State → Nat
cursorPotential (Cursor.state Cursor.active edges bits history ledger) =
  suc (length edges)
cursorPotential (Cursor.state Cursor.finished edges bits history ledger) =
  zero
cursorPotential (Cursor.state Cursor.rejected edges bits history ledger) =
  zero

module OnThreshold (thresholdLE : Word.BitWord) where

  module Machine = Threshold.ParsedThresholdMachine thresholdLE

  originalParsedRawStepStrictPotential :
    (s next : Cursor.State) →
    Machine.originalParsedRawVerifierStep s ≡ just next →
    suc (cursorPotential next) ≤ cursorPotential s
  originalParsedRawStepStrictPotential
    (Cursor.state Cursor.finished edges bits history ledger) next ()
  originalParsedRawStepStrictPotential
    (Cursor.state Cursor.rejected edges bits history ledger) next ()
  originalParsedRawStepStrictPotential
    (Cursor.state Cursor.active [] [] history ledger) next equality
    with Positive.meetsOriginalPositiveThreshold ledger thresholdLE
  ... | true with equality
  ... | refl = s≤s z≤n
  ... | false with equality
  ... | refl = s≤s z≤n
  originalParsedRawStepStrictPotential
    (Cursor.state Cursor.active [] (a ∷ bits) history ledger)
    next equality with equality
  ... | refl = s≤s z≤n
  originalParsedRawStepStrictPotential
    (Cursor.state Cursor.active (edge ∷ rest) [] history ledger)
    next equality with equality
  ... | refl = s≤s z≤n
  originalParsedRawStepStrictPotential
    (Cursor.state Cursor.active (edge ∷ rest) (a ∷ []) history ledger)
    next equality with equality
  ... | refl = s≤s z≤n
  originalParsedRawStepStrictPotential
    (Cursor.state Cursor.active
      ((Graph.raw-edge u v w , token) ∷ rest)
      (a ∷ b ∷ bits) history ledger)
    next equality
    with Original.endpointConsistent u a history
       | Original.endpointConsistent v b history
  ... | false | _ with equality
  ... | refl = s≤s z≤n
  ... | true | false with equality
  ... | refl = s≤s z≤n
  ... | true | true with equality
  ... | refl = NatP.≤-refl

  -- The exact same bound transports to the concrete ordered,
  -- first-enabled FRACTRAN source machine, not just to its reference.
  karpFirstEnabledStepStrictPotential :
    (s next : Cursor.State) →
    Machine.Compiled.directStep Machine.rules s ≡ just next →
    suc (cursorPotential next) ≤ cursorPotential s
  karpFirstEnabledStepStrictPotential s next equation =
    originalParsedRawStepStrictPotential s next
      (trans
        (sym (Machine.karpFractranFirstEnabledSameParsedRawVerifierStep s))
        equation)
