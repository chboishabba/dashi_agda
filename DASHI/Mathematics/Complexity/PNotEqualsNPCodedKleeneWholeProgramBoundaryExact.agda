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
-- `headMachine` is only the primitive-body projection; q and p are genuinely
-- distinct syntax.  But a Clay-facing realization does NOT have to compile q
-- into a separate machine code if it literally realizes the Kleene equation
--
--     run1 q x = runPrimitive2 p q x.
--
-- It is enough to run the binary body machine p on a self-delimiting tape quote
-- of the WHOLE q, or to run one fixed universal interpreter on `(code(p),q)` and
-- prove that execution equivalent.  Cook--Levin must then describe that same
-- literal machine+quote computation.  Head projection alone remains invalid,
-- while a separately compiled q-machine is optional rather than mandatory.
------------------------------------------------------------------------
