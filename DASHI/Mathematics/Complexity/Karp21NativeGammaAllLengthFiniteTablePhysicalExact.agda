{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeGammaAllLengthFiniteTablePhysicalExact where

------------------------------------------------------------------------
-- KARP-21 F1: ACTUAL FINITE TABLE for arbitrary-prefix gamma payloads.
--
-- Original source: Karp21GammaBinaryNativePayloadExact.readGammaBinary.
-- This uses the *same* bits 0^k 1 payload[k] ++ suffix.
-- The code is a literal 3-state × 4-input × 4-work-cell table;
-- no unbounded Nat parameter is consulted by any physical instruction.
--
-- On scanning each leading zero: append one Mark on the work tape.
-- At the first separator: when k=0 halt with remaining suffix;
-- when k>0 move left to the last Mark and enter payload mode.
-- For each payload bit: replace the current Mark with the bit, move
-- work-head left and input-head right.
-- When no Marks remain, halt without reading/writing a suffix bit.
-- The work-tape right-of-head then holds REVERSED payload bits,
-- followed by the original blank boundary. This is still a
-- canonical binary representation, NOT a numerical Nat decode.
--
-- IMPORTANT: full all-k bisimulation/accept-reject certificate,
-- machine clock incl. materialized input and heap, repeated-token
-- graph parser, N21 ledger/first-enabled step, F2-F4 and InNP
-- all remain OPEN. The complete-state result is not asserted by
-- a record, postulate or unproved claim.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
open import Data.Maybe.Base using (just)
open import Data.Product using (_,_)
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Original
import DASHI.Mathematics.Complexity.Karp21NativeBitTapePhysicalMachineExact as Tape
import DASHI.Mathematics.Complexity.Karp21NativeGammaOneBitPayloadPhysicalExact as K1

firstState : Fin.Fin 3
firstState = Fin.zero

zerosState : Fin.Fin 3
zerosState = Fin.suc Fin.zero

payloadState : Fin.Fin 3
payloadState = Fin.suc (Fin.suc Fin.zero)

prefixZero : Tape.Instruction 3 1
prefixZero =
  Tape.instruction zerosState Tape.B0 Tape.right
    (Tape.Mark Vec.∷ Vec.[]) (Tape.right Vec.∷ Vec.[]) false

firstSeparator : Tape.Instruction 3 1
firstSeparator =
  Tape.instruction firstState Tape.B1 Tape.right
    (Tape.Blank Vec.∷ Vec.[]) (Tape.stay Vec.∷ Vec.[]) true

laterSeparator : Tape.Instruction 3 1
laterSeparator =
  Tape.instruction payloadState Tape.B1 Tape.right
    (Tape.Blank Vec.∷ Vec.[]) (Tape.left Vec.∷ Vec.[]) false

consumeZero : Tape.Instruction 3 1
consumeZero =
  Tape.instruction payloadState Tape.B0 Tape.right
    (Tape.B0 Vec.∷ Vec.[]) (Tape.left Vec.∷ Vec.[]) false

consumeOne : Tape.Instruction 3 1
consumeOne =
  Tape.instruction payloadState Tape.B1 Tape.right
    (Tape.B1 Vec.∷ Vec.[]) (Tape.left Vec.∷ Vec.[]) false

finishB0 : Tape.Instruction 3 1
finishB0 =
  Tape.instruction payloadState Tape.B0 Tape.stay
    (Tape.Blank Vec.∷ Vec.[]) (Tape.stay Vec.∷ Vec.[]) true

finishB1 : Tape.Instruction 3 1
finishB1 =
  Tape.instruction payloadState Tape.B1 Tape.stay
    (Tape.Blank Vec.∷ Vec.[]) (Tape.stay Vec.∷ Vec.[]) true

finishBlank : Tape.Instruction 3 1
finishBlank =
  Tape.instruction payloadState Tape.Blank Tape.stay
    (Tape.Blank Vec.∷ Vec.[]) (Tape.stay Vec.∷ Vec.[]) true

rejectBlank : Tape.Instruction 3 1
rejectBlank =
  Tape.instruction payloadState Tape.Blank Tape.stay
    (Tape.Mark Vec.∷ Vec.[]) (Tape.stay Vec.∷ Vec.[]) true

rejectMarker : Tape.Instruction 3 1
rejectMarker =
  Tape.instruction payloadState Tape.Mark Tape.stay
    (Tape.Mark Vec.∷ Vec.[]) (Tape.stay Vec.∷ Vec.[]) true

firstRow : Tape.FourChoices (Tape.FourChoices (Tape.Instruction 3 1))
firstRow = Tape.four
  (K1.constantWorkRow prefixZero)
  (K1.constantWorkRow firstSeparator)
  (K1.constantWorkRow rejectBlank)
  (K1.constantWorkRow rejectMarker)

zerosRow : Tape.FourChoices (Tape.FourChoices (Tape.Instruction 3 1))
zerosRow = Tape.four
  (K1.constantWorkRow prefixZero)
  (K1.constantWorkRow laterSeparator)
  (K1.constantWorkRow rejectBlank)
  (K1.constantWorkRow rejectMarker)

payloadRow : Tape.FourChoices (Tape.FourChoices (Tape.Instruction 3 1))
payloadRow = Tape.four
  (Tape.four rejectMarker rejectMarker finishB0 consumeZero)
  (Tape.four rejectMarker rejectMarker finishB1 consumeOne)
  (Tape.four rejectMarker rejectMarker finishBlank rejectBlank)
  (Tape.four rejectMarker rejectMarker rejectMarker rejectMarker)

gammaAllLengthTable : Tape.TableProgram 3 1
gammaAllLengthTable =
  Tape.tableProgram
    (firstRow Vec.∷ zerosRow Vec.∷ payloadRow Vec.∷ Vec.[])

gammaAllLengthProgram : Tape.LocalProgram 3 1
gammaAllLengthProgram = Tape.useLiteralTable gammaAllLengthTable

startPhysicalGamma : Word.BitWord → Tape.Configuration 3 1
startPhysicalGamma bits =
  Tape.config firstState (Tape.initialInputTape bits)
    (Tape.blankTape Vec.∷ Vec.[]) false

finishZeroPrefixGamma :
  (suffix : Word.BitWord) →
  Tape.machineRun (suc zero) gammaAllLengthProgram
    (startPhysicalGamma (true ∷ suffix))
  ≡ Tape.config firstState
      (Tape.walk Tape.right
        (Tape.initialInputTape (true ∷ suffix)))
      (Tape.blankTape Vec.∷ Vec.[]) true
finishZeroPrefixGamma [] = refl
finishZeroPrefixGamma (false ∷ suffix) = refl
finishZeroPrefixGamma (true ∷ suffix) = refl

-- Source parser, all k, unchanged and genuinely original. This is NOT
-- yet the comparison of the two *full physical configurations*.
sourceAllLengthGammaWordExact :
  (payload suffix : Word.BitWord) →
  Gamma.readGammaBinary
    (Original.zeroPrefix (Data.List.Base.length payload)
      Data.List.Base.++ (true ∷
        (payload Data.List.Base.++ suffix)))
    ≡ just (true ∷ payload , suffix)
sourceAllLengthGammaWordExact = Gamma.readGammaBinaryPayloadExact

-- Unlike a higher-order "gamma parser instruction", this is a real
-- tape/cell bound on EVERY fuelled execution of our finite table.
-- A complete-machine *polynomial* clock still requires the physical
-- all-k parser equivalence, full original N21 compiler and cost join.
gammaAllLengthFuelledPhysicalCellBound :
  (fuel : Nat) (bits : Word.BitWord) →
  Tape.configurationCells
    (Tape.machineRun fuel gammaAllLengthProgram
      (startPhysicalGamma bits))
  ≤ Tape.configurationCells (startPhysicalGamma bits)
      + fuel * suc (suc zero)
gammaAllLengthFuelledPhysicalCellBound fuel bits =
  Tape.machineRunCellBudget fuel gammaAllLengthProgram
    (startPhysicalGamma bits)
