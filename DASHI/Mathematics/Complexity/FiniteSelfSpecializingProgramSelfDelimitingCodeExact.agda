module DASHI.Mathematics.Complexity.FiniteSelfSpecializingProgramSelfDelimitingCodeExact where

------------------------------------------------------------------------
-- SELF-DELIMITING DATA QUOTE FOR THE FINITE KLEENE PROGRAM TREE
--
-- Program execution can use one fixed interpreter if the finite program syntax
-- is supplied as data.  Tags are prefix-free over two bits and primitive leaves
-- carry the already-owned self-delimiting coded-standard-machine representation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardSelfDelimitingCodeExact as MachineCode
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Program

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

------------------------------------------------------------------------
-- Untyped program syntax used by the runtime parser.
------------------------------------------------------------------------

data RawProgram : Set where
  rawPrimitive : MachineCode.RawMachine → RawProgram
  rawSpecialized : RawProgram → RawProgram → RawProgram
  rawDiagonalized : RawProgram → RawProgram

rawProgramView :
  Program.Program Coded.CodedFiniteStandardTM → RawProgram
rawProgramView (Program.primitive machine) =
  rawPrimitive (MachineCode.rawMachineView machine)
rawProgramView (Program.specialized program static) =
  rawSpecialized (rawProgramView program) (rawProgramView static)
rawProgramView (Program.diagonalized program) =
  rawDiagonalized (rawProgramView program)

------------------------------------------------------------------------
-- Prefix tags:
--   00 primitive
--   01 specialized
--   10 diagonalized
--   11 invalid/reserved
------------------------------------------------------------------------

encodeProgram :
  Program.Program Coded.CodedFiniteStandardTM → List Bool
encodeProgram (Program.primitive machine) =
  false ∷ false ∷ MachineCode.selfDelimitingMachineCode machine
encodeProgram (Program.specialized program static) =
  false ∷ true ∷
    append (encodeProgram program) (encodeProgram static)
encodeProgram (Program.diagonalized program) =
  true ∷ false ∷ encodeProgram program

------------------------------------------------------------------------
-- Fuel is only a termination guard.  A five-node fixed point is parsed with
-- fuel five; recursive children receive strictly smaller fuel.
------------------------------------------------------------------------

decodeProgramFuel :
  Nat → List Bool → Maybe (RawProgram × List Bool)
decodeProgramFuel zero bits = nothing
decodeProgramFuel (suc fuel) [] = nothing
decodeProgramFuel (suc fuel) (first ∷ []) = nothing
decodeProgramFuel (suc fuel) (false ∷ false ∷ rest)
  with MachineCode.decodeMachine rest
... | nothing = nothing
... | just (machine , suffix) = just (rawPrimitive machine , suffix)
decodeProgramFuel (suc fuel) (false ∷ true ∷ rest)
  with decodeProgramFuel fuel rest
... | nothing = nothing
... | just (program , afterProgram) with decodeProgramFuel fuel afterProgram
...   | nothing = nothing
...   | just (static , suffix) =
      just (rawSpecialized program static , suffix)
decodeProgramFuel (suc fuel) (true ∷ false ∷ rest)
  with decodeProgramFuel fuel rest
... | nothing = nothing
... | just (program , suffix) = just (rawDiagonalized program , suffix)
decodeProgramFuel (suc fuel) (true ∷ true ∷ rest) = nothing

five : Nat
five = suc (suc (suc (suc (suc zero))))

------------------------------------------------------------------------
-- Exact quote of the concrete primitive-body Kleene fixed point.
------------------------------------------------------------------------

fixedPointProgram :
  Coded.CodedFiniteStandardTM →
  Program.Program Coded.CodedFiniteStandardTM
fixedPointProgram = Program.primitiveBodyFixedPoint

fixedPointRawView :
  Coded.CodedFiniteStandardTM → RawProgram
fixedPointRawView machine = rawProgramView (fixedPointProgram machine)

fixedPointQuote :
  Coded.CodedFiniteStandardTM → List Bool
fixedPointQuote machine = encodeProgram (fixedPointProgram machine)

fixedPointQuoteParsesExact :
  (machine : Coded.CodedFiniteStandardTM) →
  decodeProgramFuel five (fixedPointQuote machine)
  ≡ just (fixedPointRawView machine , [])
fixedPointQuoteParsesExact machine
  rewrite
    MachineCode.decodeMachineAppend
      (MachineCode.rawMachineView machine)
      (true ∷ false ∷
        (false ∷ false ∷
          MachineCode.selfDelimitingMachineCode machine))
    | MachineCode.decodeMachineAppend
        (MachineCode.rawMachineView machine)
        [] = refl

------------------------------------------------------------------------
-- MAX-CUT CONSEQUENCE
--
-- The literal five-node Kleene fixed point now has a self-delimiting finite tape
-- quotation that a fixed interpreter can consume, and a bounded first-order
-- parser recovers exactly the whole tree plus both primitive machine leaves.
-- This is the correct runtime quote object for behavioural self-reference; the
-- primitive `headMachine` projection is no longer used as a substitute for the
-- whole program quote.
------------------------------------------------------------------------
