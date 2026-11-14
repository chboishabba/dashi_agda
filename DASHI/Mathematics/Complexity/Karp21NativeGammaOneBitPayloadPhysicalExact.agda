{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeGammaOneBitPayloadPhysicalExact where

------------------------------------------------------------------------
-- Karp-21 F1: one ACTUAL full N21 Elias-gamma codeword, length k=1.
-- Literal source word = 0 1 b ++ suffix, where b is the ONE payload
-- bit. The ORIGINAL GammaSource.readGammaBinary returns
--    just (true :: b :: [], suffix).
--
-- Exact two-state / two-tape local machine:
--  1. scan B0, mark tally, advance input;
--  2. skip B1 separator, advance input;
--  3. read one payload bit, write it on work tape and halt.
-- No unary source Nat decoding, helper instruction oracle,
-- or state reset is hidden. The input suffix is preserved.
--
-- IMPORTANT: this table is ONLY certified for one zero-prefix,
-- one payload bit. Arbitrary gamma lengths and complete N21
-- parser/history/score/threshold remain the original F1/F3/F4 gates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
open import Data.Maybe.Base using (just)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Gamma
import DASHI.Mathematics.Complexity.Karp21NativeBitTapePhysicalMachineExact as Tape

scanState : Fin.Fin 2
scanState = Fin.zero

readState : Fin.Fin 2
readState = Fin.suc Fin.zero

scanAnotherZero : Tape.Instruction 2 1
scanAnotherZero =
  Tape.instruction scanState Tape.B0 Tape.right
    (Tape.Mark Vec.∷ Vec.[])
    (Tape.right Vec.∷ Vec.[]) false

skipGammaSeparator : Tape.Instruction 2 1
skipGammaSeparator =
  Tape.instruction readState Tape.B1 Tape.right
    (Tape.Blank Vec.∷ Vec.[])
    (Tape.stay Vec.∷ Vec.[]) false

readPayloadZero : Tape.Instruction 2 1
readPayloadZero =
  Tape.instruction readState Tape.B0 Tape.right
    (Tape.B0 Vec.∷ Vec.[])
    (Tape.stay Vec.∷ Vec.[]) true

readPayloadOne : Tape.Instruction 2 1
readPayloadOne =
  Tape.instruction readState Tape.B1 Tape.right
    (Tape.B1 Vec.∷ Vec.[])
    (Tape.stay Vec.∷ Vec.[]) true

badGammaBoundary : Tape.Instruction 2 1
badGammaBoundary =
  Tape.instruction scanState Tape.Blank Tape.stay
    (Tape.Blank Vec.∷ Vec.[])
    (Tape.stay Vec.∷ Vec.[]) true

badPayloadBoundary : Tape.Instruction 2 1
badPayloadBoundary =
  Tape.instruction readState Tape.Blank Tape.stay
    (Tape.Blank Vec.∷ Vec.[])
    (Tape.stay Vec.∷ Vec.[]) true

constantWorkRow :
  Tape.Instruction 2 1 →
  Tape.FourChoices (Tape.Instruction 2 1)
constantWorkRow ins = Tape.four ins ins ins ins

scanTable :
  Tape.FourChoices (Tape.FourChoices (Tape.Instruction 2 1))
scanTable = Tape.four
  (constantWorkRow scanAnotherZero)
  (constantWorkRow skipGammaSeparator)
  (constantWorkRow badGammaBoundary)
  (constantWorkRow badGammaBoundary)

payloadTable :
  Tape.FourChoices (Tape.FourChoices (Tape.Instruction 2 1))
payloadTable = Tape.four
  (constantWorkRow readPayloadZero)
  (constantWorkRow readPayloadOne)
  (constantWorkRow badPayloadBoundary)
  (constantWorkRow badPayloadBoundary)

literalOneBitGammaTable : Tape.TableProgram 2 1
literalOneBitGammaTable =
  Tape.tableProgram (scanTable Vec.∷ payloadTable Vec.∷ Vec.[])

oneBitGammaProgram : Tape.LocalProgram 2 1
oneBitGammaProgram = Tape.useLiteralTable literalOneBitGammaTable

-- First of the one-zero codewords, on the literal source input tape.
startOneBitGamma :
  (b : Bool) (suffix : Word.BitWord) →
  Tape.Configuration 2 1
startOneBitGamma b suffix =
  Tape.config scanState
    (Tape.initialInputTape (false ∷ true ∷ b ∷ suffix))
    (Tape.blankTape Vec.∷ Vec.[]) false

inputAfterPayload :
  (b : Bool) (suffix : Word.BitWord) → Tape.Tape
inputAfterPayload b [] =
  Tape.tape
    (Tape.encodeBit b ∷ Tape.B1 ∷ Tape.B0 ∷ [])
    Tape.Blank []
inputAfterPayload b (next ∷ rest) =
  Tape.tape
    (Tape.encodeBit b ∷ Tape.B1 ∷ Tape.B0 ∷ [])
    (Tape.encodeBit next) (Tape.encodeBits rest)

-- The tally mark from prefix scanning remains physically present
-- to the left of the one-bit payload value at the work-tape head.
finishedOneBitGamma :
  (b : Bool) (suffix : Word.BitWord) →
  Tape.Configuration 2 1
finishedOneBitGamma b suffix =
  Tape.config readState
    (inputAfterPayload b suffix)
    (Tape.tape (Tape.Mark ∷ [])
      (Tape.encodeBit b) [] Vec.∷ Vec.[]) true

-- Actual 3 instruction steps, one prefix scan + separator + payload.
physicalOneBitGammaFullRunExact :
  (b : Bool) (suffix : Word.BitWord) →
  Tape.machineRun (suc (suc (suc zero)))
    oneBitGammaProgram (startOneBitGamma b suffix)
  ≡ finishedOneBitGamma b suffix
physicalOneBitGammaFullRunExact false [] = refl
physicalOneBitGammaFullRunExact true [] = refl
physicalOneBitGammaFullRunExact false (false ∷ suffix) = refl
physicalOneBitGammaFullRunExact false (true ∷ suffix) = refl
physicalOneBitGammaFullRunExact true (false ∷ suffix) = refl
physicalOneBitGammaFullRunExact true (true ∷ suffix) = refl

-- On precisely the same ORIGINAL binary gamma word, this is the
-- ACTUAL source parser's result, not an invented numeric receipt.
originalOneBitGammaSourceExact :
  (b : Bool) (suffix : Word.BitWord) →
  Gamma.readGammaBinary (false ∷ true ∷ b ∷ suffix)
    ≡ just (true ∷ b ∷ [] , suffix)
originalOneBitGammaSourceExact false suffix = refl
originalOneBitGammaSourceExact true suffix = refl

-- Reuse the existing physical-k-tape cell-budget theorem,
-- with 3 literal machine instructions and ONE work tape.
physicalOneBitGammaTotalCellBudget :
  (b : Bool) (suffix : Word.BitWord) →
  Tape.configurationCells
    (Tape.machineRun (suc (suc (suc zero)))
      oneBitGammaProgram (startOneBitGamma b suffix))
  ≤ Tape.configurationCells (startOneBitGamma b suffix)
    + ((suc (suc (suc zero))) * suc (suc zero))
physicalOneBitGammaTotalCellBudget b suffix =
  Tape.machineRunCellBudget (suc (suc (suc zero)))
    oneBitGammaProgram (startOneBitGamma b suffix)
