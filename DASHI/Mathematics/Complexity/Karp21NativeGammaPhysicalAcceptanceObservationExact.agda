{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeGammaPhysicalAcceptanceObservationExact where

------------------------------------------------------------------------
-- F1.5: PHYSICAL ACCEPTANCE OBSERVATION ON THE LITERAL GAMMA TABLE.
--
-- The real finite table stores a *halt* flag, not an accept/reject
-- field. A halted gamma parser succeeds iff its work-head is Blank.
-- Rejection rows halt with Mark at the work head. This source-native
-- observation distinguishes an empty or truncated code from the
-- successfully completed 0^k 1 payload source while preserving
-- exact original input suffix and the existing physical state.
--
-- This settles an observation seam, NOT full all-words parser
-- equivalence or N21 F3/F4 cost/heap/NP.
-- Safe finite reduction. Pinned Agda 2.9 kernel check required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (zero; suc; _+_)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Vec.Base as Vec
import Data.List.Base as List
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Original

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21NativeBitTapePhysicalMachineExact as Tape
import DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthFiniteTablePhysicalExact as Gamma
import DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthCompositePhysicalExact as Composite

isBlank : Tape.Cell → Bool
isBlank Tape.Blank = true
isBlank Tape.B0 = false
isBlank Tape.B1 = false
isBlank Tape.Mark = false

physicalGammaAccepts : Tape.Configuration 3 1 → Bool
physicalGammaAccepts
  (Tape.config state input (work Vec.∷ Vec.[]) false) = false
physicalGammaAccepts
  (Tape.config state input (work Vec.∷ Vec.[]) true) =
  isBlank (Tape.atHead work)

-- The original k=0 gamma code (leading separator one) is accepted,
-- retaining the arbitrary source suffix at the tape head.
physicalZeroLengthGammaAccepted :
  (suffix : Word.BitWord) →
  physicalGammaAccepts
    (Tape.machineRun (suc zero) Gamma.gammaAllLengthProgram
      (Gamma.startPhysicalGamma (true ∷ suffix))) ≡ true
physicalZeroLengthGammaAccepted suffix
  rewrite Gamma.finishZeroPrefixGamma suffix = refl

-- Every genuinely positive gamma payload has a source-written
-- full-table run of 2k+2 instructions; its halted work head is Blank.
-- Note: this is a semantic OBSERVATION, not an N21 decision bit.
physicalPositiveGammaAccepted :
  (first : Bool) (rest suffix : Word.BitWord) →
  let k = suc (List.length rest)
      payload = first ∷ rest
      inputWord =
        List._++_
          (Original.zeroPrefix k)
          (true ∷ List._++_ payload suffix)
  in
  physicalGammaAccepts
    (Tape.machineRun (k + (suc (k + suc zero)))
      Gamma.gammaAllLengthProgram (Gamma.startPhysicalGamma inputWord))
    ≡ true
physicalPositiveGammaAccepted first rest suffix
  rewrite Composite.physicalAllLengthGammaRunSameOriginalPositive
    first rest suffix = refl

-- A missing leading separator is rejected by an actual first-state
-- table instruction (the rejectBlank row writes Mark to work head).
physicalEmptyInputRejected :
  physicalGammaAccepts
    (Tape.machineRun (suc zero) Gamma.gammaAllLengthProgram
      (Gamma.startPhysicalGamma [])) ≡ false
physicalEmptyInputRejected = refl

-- A zero prefix without any 1 separator is rejected after two real
-- table instructions, rather than spuriously decoded as gamma(1).
physicalLoneZeroRejected :
  physicalGammaAccepts
    (Tape.machineRun (suc (suc zero)) Gamma.gammaAllLengthProgram
      (Gamma.startPhysicalGamma (false ∷ []))) ≡ false
physicalLoneZeroRejected = refl
