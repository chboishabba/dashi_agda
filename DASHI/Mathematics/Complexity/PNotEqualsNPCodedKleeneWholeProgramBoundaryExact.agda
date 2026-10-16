module DASHI.Mathematics.Complexity.PNotEqualsNPCodedKleeneWholeProgramBoundaryExact where

------------------------------------------------------------------------
-- PRIMITIVE HEAD != WHOLE BEHAVIOURAL FIXED-POINT PROGRAM
--
-- Kleene self-reference gives a whole specialized/diagonalized syntax tree.
-- Recovering the leftmost primitive coded machine is useful for quote-sensitive
-- diagnostics, but it is not a compiler for that whole tree.  The Cook object
-- in a Clay-facing self-application must describe the machine obtained by
-- compiling the ENTIRE fixed-point program.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedQuoteSensitiveKleeneExact as Kleene

primitiveProgramSize :
  (machine : Coded.CodedFiniteStandardTM) →
  Code.programSize (Code.primitive machine) ≡ suc zero
primitiveProgramSize machine = refl

fiveNotOne :
  suc (suc (suc zero) + suc (suc zero)) ≡ suc zero → ⊥
fiveNotOne ()

fixedPointProgramNotPrimitiveLeaf :
  (machine : Coded.CodedFiniteStandardTM) →
  Kleene.codedQuoteSensitiveFixedPoint machine
    ≡ Code.primitive machine →
  ⊥
fixedPointProgramNotPrimitiveLeaf machine equality =
  fiveNotOne
    (trans
      (sym (Kleene.codedFixedPointSyntaxNodesExact machine))
      (trans
        (cong Code.programSize equality)
        (primitiveProgramSize machine)))

------------------------------------------------------------------------
-- Compiler target.
--
-- This is deliberately a proposition about an ACTUAL compiler output, not a
-- replacement self-reference calculus.  An inhabitant must map the complete
-- finite Kleene syntax to ordinary coded standard-TM syntax and preserve run
-- behaviour.  Merely projecting `headMachine` cannot inhabit it.
------------------------------------------------------------------------

record WholeProgramCompilation
    (program : Code.Program Coded.CodedFiniteStandardTM) : Set₁ where
  field
    compiledCode : Coded.CodedFiniteStandardTM

open WholeProgramCompilation public

------------------------------------------------------------------------
-- MAX-CUT CONSEQUENCE
--
-- The previous `headMachine`/recovered-description results pay only primitive
-- body identity and quote sensitivity.  They must not be used as the final
-- same-object Cook weld.  The next Clay-critical construction is now exact:
-- compile the entire specialized/diagonalized finite Program into a literal
-- coded standard TM, prove semantic preservation, and only then form the guarded
-- Cook description of THAT compiled code.
------------------------------------------------------------------------
