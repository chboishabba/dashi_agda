{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthSeparatorAndHaltExact where

------------------------------------------------------------------------
-- F1 all-k ACTUAL finite-table gamma separator and exit transitions.
-- Original same source:
--  Karp21NativeGammaAllLengthFiniteTablePhysicalExact
--  Karp21NativeGammaAllLengthPrefixSimulationExact
--  Karp21NativeGammaAllLengthPayloadSimulationExact.
--
-- For the k>=1 original positive gamma code, k prefix Mark cells
-- become a payload work-tape head on the FIRST Mark after the B1
-- separator, and finishing when all k Mark cells are consumed
-- leaves the original suffix under the unmodified input head.
--
-- These prove the two actual physical instructions needed to weld
-- all-prefix and all-payload induction. The final total-run count
-- and source-decoder bisimulation are still separate until composed
-- and kernel checked; no axiom or arbitrary instruction oracle.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Data.List.Base as List
import Data.Vec.Base as Vec

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21NativeBitTapePhysicalMachineExact as Tape
import DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthFiniteTablePhysicalExact as Gamma
import DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthPrefixSimulationExact as Prefix
import DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthPayloadSimulationExact as Payload

-- Exactly n new Mark cells are prepended; prepending an additional
-- Mark commutes with this recurrence because all cells are Mark.
pushMarksMark :
  (n : Nat) (prior : List Tape.Cell) →
  Prefix.pushMarks n (Tape.Mark ∷ prior)
  ≡ Tape.Mark ∷ Prefix.pushMarks n prior
pushMarksMark zero prior = refl
pushMarksMark (suc n) prior =
  pushMarksMark n (Tape.Mark ∷ prior)

pushMarksIsMarks :
  (n : Nat) →
  Prefix.pushMarks n [] ≡ Payload.marks n
pushMarksIsMarks zero = refl
pushMarksIsMarks (suc n) =
  trans
    (pushMarksMark n [])
    (cong (Tape.Mark ∷_) (pushMarksIsMarks n))

-- The physical k=n+1 zero scan leaves the exact k Mark tally,
-- no unaccounted free count field or integer magnitude.
wholePrefixWorkMarksExact :
  (n : Nat) →
  Prefix.pushMarks n (Tape.Mark ∷ [])
    ≡ Tape.Mark ∷ Payload.marks n
wholePrefixWorkMarksExact n =
  trans (pushMarksMark n [])
    (cong (Tape.Mark ∷_) (pushMarksIsMarks n))

-- The selected real finite-table separator step:
-- B1, Mark + k-1 further Marks => head moves left to last Mark,
-- while the first actual payload bit reaches input head.
physicalSeparatorToOriginalPayload :
  (inputLeft : List Tape.Cell)
  (first : Bool) (rest suffix : Word.BitWord) →
  Tape.machineStep Gamma.gammaAllLengthProgram
    (Prefix.scanConfiguration zero inputLeft
      (Tape.Mark ∷ Payload.marks (List.length rest))
      (first ∷ rest) suffix)
  ≡
  Payload.payloadConfiguration
    (Tape.B1 ∷ inputLeft) (Tape.Blank ∷ [])
    (first ∷ rest) suffix
physicalSeparatorToOriginalPayload inputLeft false rest suffix = refl
physicalSeparatorToOriginalPayload inputLeft true rest suffix = refl

-- Last selected work head has become Blank, but the original
-- suffix head (if any) is visible. The finite table halts without
-- consuming that first suffix symbol.
physicalGammaCompletionPreservesSuffix :
  (inputLeft workRight : List Tape.Cell)
  (suffix : Word.BitWord) →
  Tape.machineStep Gamma.gammaAllLengthProgram
    (Payload.payloadConfiguration
      inputLeft workRight [] suffix)
  ≡
  Tape.config Gamma.payloadState
    (Payload.inputAt inputLeft suffix)
    (Payload.workWithRemainingMarks zero workRight Vec.∷ Vec.[])
    true
physicalGammaCompletionPreservesSuffix inputLeft workRight [] = refl
physicalGammaCompletionPreservesSuffix inputLeft workRight (false ∷ tail) = refl
physicalGammaCompletionPreservesSuffix inputLeft workRight (true ∷ tail) = refl
