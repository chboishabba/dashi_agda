{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthPrefixSimulationExact where

------------------------------------------------------------------------
-- F1 ALL-k ORIGINAL GAMMA ZERO-PREFIX PHYSICAL TABLE SIMULATION.
--
-- Reuses Karp21NativeGammaAllLengthFiniteTablePhysicalExact's
-- literal 3-state table and one physical work tape, never a
-- higher-order read-gamma instruction or numeric Nat parser.
--
-- For arbitrary n further zero bits, the first prefix-zero
-- transition and all n remaining transitions push precisely
-- n+1 physical B0 symbols to the input zipper's left and
-- n+1 Mark symbols to the work zipper's left.
--
-- Original source parser is GammaBinaryNativePayloadExact.
-- The separator/payload composition and full all-k step-clock
-- are still independent F1/F3/F4 obligations.
--
-- Source-written, no postulates; exact-head Agda 2.9 kernel open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.List.Base as List
import Data.Vec.Base as Vec

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Original
import DASHI.Mathematics.Complexity.Karp21NativeBitTapePhysicalMachineExact as Tape
import DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthFiniteTablePhysicalExact as Gamma
import DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthPayloadSimulationExact as Payload

remainingPrefix :
  Nat → Word.BitWord → Word.BitWord → Word.BitWord
remainingPrefix remaining payload suffix =
  List._++_ (Original.zeroPrefix remaining)
    (true ∷ List._++_ payload suffix)

scanConfiguration :
  Nat → List Tape.Cell → List Tape.Cell →
  Word.BitWord → Word.BitWord →
  Tape.Configuration 3 1
scanConfiguration remaining inputLeft workLeft payload suffix =
  Tape.config Gamma.zerosState
    (Payload.inputAt inputLeft
      (remainingPrefix remaining payload suffix))
    (Tape.tape workLeft Tape.Blank []
      Vec.∷ Vec.[])
    false

-- Exactly one literal 3-state finite-table step per remaining B0.
physicalNextPrefixZero :
  (n : Nat)
  (inputLeft workLeft : List Tape.Cell)
  (payload suffix : Word.BitWord) →
  Tape.machineStep Gamma.gammaAllLengthProgram
    (scanConfiguration (suc n) inputLeft workLeft payload suffix)
  ≡ scanConfiguration n
      (Tape.B0 ∷ inputLeft)
      (Tape.Mark ∷ workLeft)
      payload suffix
physicalNextPrefixZero zero inputLeft workLeft payload suffix = refl
physicalNextPrefixZero (suc n) inputLeft workLeft payload suffix = refl

pushZeros : Nat → List Tape.Cell → List Tape.Cell
pushZeros zero left = left
pushZeros (suc n) left = pushZeros n (Tape.B0 ∷ left)

pushMarks : Nat → List Tape.Cell → List Tape.Cell
pushMarks zero left = left
pushMarks (suc n) left = pushMarks n (Tape.Mark ∷ left)

-- Arbitrary count of literal prefix-zero instructions on
-- the already-selected zero-scan physical state.
physicalAllRemainingPrefixZerosExact :
  (n : Nat)
  (inputLeft workLeft : List Tape.Cell)
  (payload suffix : Word.BitWord) →
  Tape.machineRun n Gamma.gammaAllLengthProgram
    (scanConfiguration n inputLeft workLeft payload suffix)
  ≡
  scanConfiguration zero
    (pushZeros n inputLeft)
    (pushMarks n workLeft)
    payload suffix
physicalAllRemainingPrefixZerosExact
  zero inputLeft workLeft payload suffix = refl
physicalAllRemainingPrefixZerosExact
  (suc n) inputLeft workLeft payload suffix
  rewrite physicalNextPrefixZero n inputLeft workLeft payload suffix =
  physicalAllRemainingPrefixZerosExact
    n (Tape.B0 ∷ inputLeft) (Tape.Mark ∷ workLeft)
    payload suffix

-- The first physical B0 step switches from firstState to
-- zerosState, charging one new mark and one input move.
physicalFirstPrefixZero :
  (n : Nat) (payload suffix : Word.BitWord) →
  Tape.machineStep Gamma.gammaAllLengthProgram
    (Gamma.startPhysicalGamma
      (false ∷ remainingPrefix n payload suffix))
  ≡ scanConfiguration n
      (Tape.B0 ∷ [])
      (Tape.Mark ∷ [])
      payload suffix
physicalFirstPrefixZero zero payload suffix = refl
physicalFirstPrefixZero (suc n) payload suffix = refl

-- For EVERY k=n+1, the physical prefix stage consumes the
-- entire zero-run in exactly k finite instructions and leaves
-- the first B1 separator under the input head, preserving
-- all payload+suffix symbols. The next step is the separator.
physicalWholePrefixZeroRunExact :
  (n : Nat) (payload suffix : Word.BitWord) →
  Tape.machineRun (suc n) Gamma.gammaAllLengthProgram
    (Gamma.startPhysicalGamma
      (false ∷ remainingPrefix n payload suffix))
  ≡
  scanConfiguration zero
    (pushZeros n (Tape.B0 ∷ []))
    (pushMarks n (Tape.Mark ∷ []))
    payload suffix
physicalWholePrefixZeroRunExact n payload suffix
  rewrite physicalFirstPrefixZero n payload suffix =
  physicalAllRemainingPrefixZerosExact
    n (Tape.B0 ∷ []) (Tape.Mark ∷ [])
    payload suffix
