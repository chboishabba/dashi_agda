module DASHI.Physics.Closure.NSTriadKNDeterministicNestedColumnRound331Exact where

------------------------------------------------------------------------
-- ROUND331 / REVERSE NESTED COLUMN GEOMETRY IS OUTPUT-DETERMINISTIC
--
-- Row enumeration (R330) is a dependent sum and therefore carries real
-- multiplicity.  Reverse the question before trying to estimate a column.
--
-- Fix an inner incidence a+b=p and the remaining outer input q.  Resonance
-- forces the final output
--
--   k = p+q = (a+b)+q.
--
-- Thus there is no independent output choice on the reverse carrier.  The
-- primitive physical triad enumeration is also no-duplicate in its ordered
-- input pair, so duplicate output witnesses are not a hidden combinatorial
-- source.  This does NOT yet prove the numerical column budget: heat weights,
-- shell routing and input-mass bookkeeping still have to be aggregated.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical

determinedOuterOutput :
  Physical.PhysicalTriadIncidence → Z3.FourierMode → Z3.FourierMode
determinedOuterOutput inner outerQ =
  Z3.addMode (Physical.k inner) outerQ

nestedOuterOutputIsDetermined :
  (inner outer : Physical.PhysicalTriadIncidence) →
  Physical.k inner ≡ Physical.p outer →
  Physical.k outer ≡ determinedOuterOutput inner (Physical.q outer)
nestedOuterOutputIsDetermined inner outer glue =
  trans
    (sym (Physical.resonance outer))
    (cong (λ p → Z3.addMode p (Physical.q outer)) (sym glue))

sameInnerAndOuterQForceSameFinalOutput :
  (inner outer₁ outer₂ : Physical.PhysicalTriadIncidence) →
  Physical.k inner ≡ Physical.p outer₁ →
  Physical.k inner ≡ Physical.p outer₂ →
  Physical.q outer₁ ≡ Physical.q outer₂ →
  Physical.k outer₁ ≡ Physical.k outer₂
sameInnerAndOuterQForceSameFinalOutput inner outer₁ outer₂ glue₁ glue₂ qSame =
  trans
    (nestedOuterOutputIsDetermined inner outer₁ glue₁)
    (trans
      (cong (determinedOuterOutput inner) qSame)
      (sym (nestedOuterOutputIsDetermined inner outer₂ glue₂)))

round331ReverseColumnOutputDeterminedByInnerAndQ : Bool
round331ReverseColumnOutputDeterminedByInnerAndQ = true

round331PrimitiveTriadEnumerationNoDuplicatesAvailable : Bool
round331PrimitiveTriadEnumerationNoDuplicatesAvailable = true

round331IndependentOutputMultiplicityRemains : Bool
round331IndependentOutputMultiplicityRemains = false

round331NumericalWeightedColumnBudgetClosed : Bool
round331NumericalWeightedColumnBudgetClosed = false

round331RowBudgetClosed : Bool
round331RowBudgetClosed = false

round331PackageAClosed : Bool
round331PackageAClosed = false

round331ClayPromotion : Bool
round331ClayPromotion = false
