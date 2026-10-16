module DASHI.Mathematics.Complexity.PNotEqualsNPCodedKleeneWholeProgramBoundaryExact where

------------------------------------------------------------------------
-- PRIMITIVE HEAD != WHOLE BEHAVIOURAL FIXED-POINT PROGRAM
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
-- MAX-CUT CONSEQUENCE
--
-- `headMachine`/recovered-description pays primitive-body identity only.  The
-- whole fixed-point syntax is provably a distinct object.  A Clay-facing Cook
-- weld must therefore first compile the COMPLETE specialized/diagonalized syntax
-- into ordinary coded standard-TM syntax, prove behavioural preservation, and
-- form the guarded Cook description of that compiled code.  No placeholder
-- compiler interface is introduced here.
------------------------------------------------------------------------
