module DASHI.Mathematics.Complexity.FiniteSelfSpecializingProgramQuoteSizeExact where

------------------------------------------------------------------------
-- EXACT BIT LENGTH OF THE WHOLE KLEENE FIXED-POINT QUOTATION
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardSelfDelimitingCodeExact as MachineCode
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Program
import DASHI.Mathematics.Complexity.FiniteSelfSpecializingProgramSelfDelimitingCodeExact as Quote

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendLength :
  ∀ {A : Set} (xs ys : List A) →
  listLength (Quote.append xs ys) ≡ listLength xs + listLength ys
appendLength [] ys = refl
appendLength (x ∷ xs) ys rewrite appendLength xs ys = refl

machineCodeLength : Coded.CodedFiniteStandardTM → Nat
machineCodeLength machine =
  listLength (MachineCode.selfDelimitingMachineCode machine)

programQuoteLength :
  Program.Program Coded.CodedFiniteStandardTM → Nat
programQuoteLength program = listLength (Quote.encodeProgram program)

primitiveQuoteLengthExact :
  (machine : Coded.CodedFiniteStandardTM) →
  programQuoteLength (Program.primitive machine)
  ≡ suc (suc (machineCodeLength machine))
primitiveQuoteLengthExact machine = refl

diagonalQuoteLengthExact :
  (program : Program.Program Coded.CodedFiniteStandardTM) →
  programQuoteLength (Program.diagonalized program)
  ≡ suc (suc (programQuoteLength program))
diagonalQuoteLengthExact program = refl

specializedQuoteLengthExact :
  (program static : Program.Program Coded.CodedFiniteStandardTM) →
  programQuoteLength (Program.specialized program static)
  ≡ suc (suc (programQuoteLength program + programQuoteLength static))
specializedQuoteLengthExact program static
  rewrite appendLength (Quote.encodeProgram program) (Quote.encodeProgram static) = refl

fixedPointQuoteLengthExact :
  (machine : Coded.CodedFiniteStandardTM) →
  listLength (Quote.fixedPointQuote machine)
  ≡ 10 + (2 * machineCodeLength machine)
fixedPointQuoteLengthExact machine
  rewrite specializedQuoteLengthExact
      (Program.diagonalized (Program.primitive machine))
      (Program.diagonalized (Program.primitive machine))
        | diagonalQuoteLengthExact (Program.primitive machine)
        | primitiveQuoteLengthExact machine = refl

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The dynamic behavioural-self-reference input is exact: ten constructor-tag
-- bits plus two copies of p's self-delimiting machine code. This is the static
-- quotation term to charge in the final universal-simulation resource equation.
------------------------------------------------------------------------
