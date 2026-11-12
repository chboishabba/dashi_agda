{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeGammaPrefixPhysicalSimulationExact where

------------------------------------------------------------------------
-- F1/F3 physical micro-compiler for the FIRST stage of the original
-- N21 Elias-gamma reader: scan the zero prefix up to the first 1.
--
-- IMPORTANT: The original source scanner is
-- GammaSource.scanZeros in Karp21GammaBinaryNativePayloadExact.
-- This owner implements and traces its ZERO-PREFIX part on literal
-- finite control, a read-only input head, and a unary tally work tape.
-- One physical step skips one zero and marks one tally cell.
-- One further physical step stops on the first 1.
--
-- It is a genuine finite-state, local-table, explicit physical trace;
-- it does NOT compile the payload reader, graph/edge parser, endpoint
-- history, signed ledger, threshold, or whole verifier. The full
-- originalBitTapeStepSimulatesN21Rule remains OPEN.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (_++_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Nat.Base using (_≤_)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Source
import DASHI.Mathematics.Complexity.Karp21NativeBitTapePhysicalMachineExact as Tape

-- The four input-symbol cases, independent of the observed work cell.
-- B0: advance and mark another source gamma zero.
-- B1: halt at the payload separator, without consuming it.
-- Blank/Mark: halt; they are malformed gamma-prefix boundaries.
gammaSkipZero : Tape.Instruction 1 1
gammaSkipZero =
  Tape.instruction Fin.zero Tape.B0 Tape.right
    (Tape.Mark Vec.∷ Vec.[])
    (Tape.right Vec.∷ Vec.[]) false

gammaSeeOne : Tape.Instruction 1 1
gammaSeeOne =
  Tape.instruction Fin.zero Tape.B1 Tape.stay
    (Tape.Blank Vec.∷ Vec.[])
    (Tape.stay Vec.∷ Vec.[]) true

gammaEndBlank : Tape.Instruction 1 1
gammaEndBlank =
  Tape.instruction Fin.zero Tape.Blank Tape.stay
    (Tape.Blank Vec.∷ Vec.[])
    (Tape.stay Vec.∷ Vec.[]) true

gammaEndMark : Tape.Instruction 1 1
gammaEndMark =
  Tape.instruction Fin.zero Tape.Mark Tape.stay
    (Tape.Blank Vec.∷ Vec.[])
    (Tape.stay Vec.∷ Vec.[]) true

-- In the physical carrier, the OUTER FourChoices selects the input
-- head, and the INNER FourChoices selects the work head. Reversing
-- this indexing incorrectly makes an input B0 with blank work head
-- execute the Blank-halting instruction.
constantWorkRow :
  Tape.Instruction 1 1 →
  Tape.FourChoices (Tape.Instruction 1 1)
constantWorkRow action = Tape.four action action action action

gammaWorkCases :
  Tape.FourChoices (Tape.FourChoices (Tape.Instruction 1 1))
gammaWorkCases =
  Tape.four
    (constantWorkRow gammaSkipZero)
    (constantWorkRow gammaSeeOne)
    (constantWorkRow gammaEndBlank)
    (constantWorkRow gammaEndMark)

literalGammaPrefixTable : Tape.TableProgram 1 1
literalGammaPrefixTable =
  Tape.tableProgram (gammaWorkCases Vec.∷ Vec.[])

gammaPrefixProgram : Tape.LocalProgram 1 1
gammaPrefixProgram = Tape.useLiteralTable literalGammaPrefixTable

-- Exact physical dispatch by BOTH observed symbols; this is a
-- 16-case definitional verification of the literal table order.
gammaTableB0IgnoresWork :
  (workHead : Tape.Cell) →
  Tape.tableInstruction literalGammaPrefixTable
    Fin.zero Tape.B0 (workHead Vec.∷ Vec.[])
  ≡ gammaSkipZero
gammaTableB0IgnoresWork Tape.B0 = refl
gammaTableB0IgnoresWork Tape.B1 = refl
gammaTableB0IgnoresWork Tape.Blank = refl
gammaTableB0IgnoresWork Tape.Mark = refl

gammaTableB1IgnoresWork :
  (workHead : Tape.Cell) →
  Tape.tableInstruction literalGammaPrefixTable
    Fin.zero Tape.B1 (workHead Vec.∷ Vec.[])
  ≡ gammaSeeOne
gammaTableB1IgnoresWork Tape.B0 = refl
gammaTableB1IgnoresWork Tape.B1 = refl
gammaTableB1IgnoresWork Tape.Blank = refl
gammaTableB1IgnoresWork Tape.Mark = refl

gammaTableBlankIgnoresWork :
  (workHead : Tape.Cell) →
  Tape.tableInstruction literalGammaPrefixTable
    Fin.zero Tape.Blank (workHead Vec.∷ Vec.[])
  ≡ gammaEndBlank
gammaTableBlankIgnoresWork Tape.B0 = refl
gammaTableBlankIgnoresWork Tape.B1 = refl
gammaTableBlankIgnoresWork Tape.Blank = refl
gammaTableBlankIgnoresWork Tape.Mark = refl

gammaTableMarkIgnoresWork :
  (workHead : Tape.Cell) →
  Tape.tableInstruction literalGammaPrefixTable
    Fin.zero Tape.Mark (workHead Vec.∷ Vec.[])
  ≡ gammaEndMark
gammaTableMarkIgnoresWork Tape.B0 = refl
gammaTableMarkIgnoresWork Tape.B1 = refl
gammaTableMarkIgnoresWork Tape.Blank = refl
gammaTableMarkIgnoresWork Tape.Mark = refl

-- The work tally head is always on blank; the left list is a literal
-- sequence of tally marks. The input head is at the next source bit.
scanning :
  List Tape.Cell → List Tape.Cell → Word.BitWord →
  Tape.Configuration 1 1
scanning left tally [] =
  Tape.config Fin.zero
    (Tape.tape left Tape.Blank [])
    (Tape.tape tally Tape.Blank [] Vec.∷ Vec.[])
    false
scanning left tally (bit ∷ rest) =
  Tape.config Fin.zero
    (Tape.tape left (Tape.encodeBit bit) (Tape.encodeBits rest))
    (Tape.tape tally Tape.Blank [] Vec.∷ Vec.[])
    false

stopped :
  List Tape.Cell → List Tape.Cell → Word.BitWord →
  Tape.Configuration 1 1
stopped left tally payload =
  Tape.config Fin.zero
    (Tape.tape left Tape.B1 (Tape.encodeBits payload))
    (Tape.tape tally Tape.Blank [] Vec.∷ Vec.[])
    true

-- Definitional micro-simulation: the physical head advances over one
-- literal zero while recording EXACTLY one mark in the tally tape.
onePhysicalGammaZero :
  (left tally : List Tape.Cell) (rest : Word.BitWord) →
  Tape.machineStep gammaPrefixProgram
    (scanning left tally (false ∷ rest))
  ≡ scanning (Tape.B0 ∷ left) (Tape.Mark ∷ tally) rest
onePhysicalGammaZero left tally [] = refl
onePhysicalGammaZero left tally (false ∷ rest) = refl
onePhysicalGammaZero left tally (true ∷ rest) = refl

-- Separator observation is a separate physical instruction; it does
-- not consume the leading 1 or any payload bit.
onePhysicalGammaSeparator :
  (left tally : List Tape.Cell) (payload : Word.BitWord) →
  Tape.machineStep gammaPrefixProgram
    (scanning left tally (true ∷ payload))
  ≡ stopped left tally payload
onePhysicalGammaSeparator left tally payload = refl

-- Exact number of physical ZERO-skipping instructions on a literal
-- source Elias prefix. The existential lists preserve both head-left
-- histories without relying on any arbitrary Nat decoding.
physicalGammaZerosExact :
  (zeros : Nat)
  (left tally : List Tape.Cell)
  (payload : Word.BitWord) →
  Σ (List Tape.Cell × List Tape.Cell)
    (λ final →
      Tape.machineRun zeros gammaPrefixProgram
        (scanning left tally
          (Gamma.zeroPrefix zeros ++ (true ∷ payload)))
      ≡ scanning (proj₁ final) (proj₂ final) (true ∷ payload))
physicalGammaZerosExact zero left tally payload =
  (left , tally) , refl
physicalGammaZerosExact (suc zeros) left tally payload
  with physicalGammaZerosExact zeros
    (Tape.B0 ∷ left) (Tape.Mark ∷ tally) payload
... | final , recurrence
  rewrite onePhysicalGammaZero left tally
    (Gamma.zeroPrefix zeros ++ (true ∷ payload)) =
  final , recurrence

-- The actual source readGammaBinary first scans these same k zeros.
-- The fully literal table halts after k+1 physical instructions,
-- keeping the first 1 at the input head.
physicalGammaPrefixHaltExact :
  (zeros : Nat) (payload : Word.BitWord) →
  Σ (List Tape.Cell × List Tape.Cell)
    (λ final →
      Tape.machineRun (suc zeros) gammaPrefixProgram
        (scanning [] []
          (Gamma.zeroPrefix zeros ++ (true ∷ payload)))
      ≡ stopped (proj₁ final) (proj₂ final) payload)
physicalGammaPrefixHaltExact zeros payload
  with physicalGammaZerosExact zeros [] [] payload
... | final , exact =
  final ,
    trans
      (Tape.machineRunAppendOne zeros gammaPrefixProgram
        (scanning [] []
          (Gamma.zeroPrefix zeros ++ (true ∷ payload))))
      (trans
        (cong (Tape.machineStep gammaPrefixProgram) exact)
        (onePhysicalGammaSeparator
          (proj₁ final) (proj₂ final) payload))

-- Same ACTUAL source gamma scan stage, not a fabricated parser.
sourceGammaZeroPrefixAgreement :
  (zeros : Nat) (payload : Word.BitWord) →
  Source.scanZeros zero
    (Gamma.zeroPrefix zeros ++ (true ∷ payload))
  ≡ Source.scanZeros zeros (true ∷ payload)
sourceGammaZeroPrefixAgreement zeros payload =
  Source.scanZerosPrefixExact zero zeros payload

-- Proven physical footprint for this SAME literal finite-table run.
-- This is an F1/F2 partial budget, NOT a cost for the full gamma
-- payload decoder or N21 verifier. There are two physical tapes.
physicalGammaPrefixCellBudget :
  (zeros : Nat) (payload : Word.BitWord) →
  Tape.configurationCells
    (Tape.machineRun (suc zeros) gammaPrefixProgram
      (scanning [] []
        (Gamma.zeroPrefix zeros ++ (true ∷ payload))))
  ≤ Tape.configurationCells
      (scanning [] []
        (Gamma.zeroPrefix zeros ++ (true ∷ payload)))
      + (suc zeros * suc (suc zero))
physicalGammaPrefixCellBudget zeros payload =
  Tape.machineRunCellBudget (suc zeros) gammaPrefixProgram
    (scanning [] []
      (Gamma.zeroPrefix zeros ++ (true ∷ payload)))
