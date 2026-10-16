module DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityClosureExact where

------------------------------------------------------------------------
-- THIN CLOSURE / QUIESCENCE OWNER FOR UNARY-FIELD EQUALITY
--
-- Canonical dispatch authority lives in
-- `CodedFiniteUnaryFieldEqualityDeterminismExact`.  This module deliberately
-- does not re-prove it.  It reuses that single owner, exposes the decoded
-- standard machine, and pays the quiescent result-sink facts needed downstream.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (nothing)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityExact as Equality
import DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityDeterminismExact as Determinism

------------------------------------------------------------------------
-- 1. Reuse the canonical deterministic coded machine; no duplicate authority.
------------------------------------------------------------------------

fieldEqualityDispatchUnique :
  ∀ {left right :
      Local.TapeRule
        (Fin.Fin Equality.stateCount)
        (Fin.Fin Equality.symbolCount)} →
  Local.RuleOccurs left Equality.rules →
  Local.RuleOccurs right Equality.rules →
  Local.sourceState left ≡ Local.sourceState right →
  Local.readSymbol left ≡ Local.readSymbol right →
  left ≡ right
fieldEqualityDispatchUnique = Determinism.dispatchUnique

fieldEqualityCode : Coded.CodedFiniteStandardTM
fieldEqualityCode = Determinism.equalityCode

fieldEqualityMachine :
  Standard.StandardSingleTapeMachine
    (Fin.Fin Equality.stateCount)
    (Fin.Fin Equality.symbolCount)
fieldEqualityMachine =
  Presented.finitePresentedStandardMachine
    (Coded.decodeCodedStandardTM fieldEqualityCode)

------------------------------------------------------------------------
-- 2. Both result sinks are quiescent in the canonical closed machine.
------------------------------------------------------------------------

equalSinkQuiescent :
  (symbol : Fin.Fin Equality.symbolCount) →
  Standard.transition fieldEqualityMachine Equality.equalState symbol ≡ nothing
equalSinkQuiescent Fin.zero = refl
equalSinkQuiescent (Fin.suc Fin.zero) = refl
equalSinkQuiescent (Fin.suc (Fin.suc Fin.zero)) = refl
equalSinkQuiescent (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = refl
equalSinkQuiescent (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = refl

unequalSinkQuiescent :
  (symbol : Fin.Fin Equality.symbolCount) →
  Standard.transition fieldEqualityMachine Equality.unequalState symbol ≡ nothing
unequalSinkQuiescent Fin.zero = refl
unequalSinkQuiescent (Fin.suc Fin.zero) = refl
unequalSinkQuiescent (Fin.suc (Fin.suc Fin.zero)) = refl
unequalSinkQuiescent (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = refl
unequalSinkQuiescent (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = refl

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- There is now one theorem authority for equality dispatch (`Determinism`), one
-- canonical coded machine, and this thin closure only supplies downstream
-- standard-machine/quiescence views.  The remaining substantive equality leaf
-- is run-level correctness/work for the mark/shuttle algorithm.
------------------------------------------------------------------------
