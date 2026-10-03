module DASHI.ComputerScience.TekumSuccessorCarrySplitExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Base using (_++_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumBalancedSuccessorExact as Succ

------------------------------------------------------------------------
-- GENERIC FIELD-CARRY NORMAL FORM
--
-- An anchor is read LST first as
--
--   fraction ++ exponent ++ regime.
--
-- These theorems are independent of the regime-dependent field lengths. They
-- expose exactly the three cases used in Hunhold Proposition 4:
--   1. carry stops inside the fraction;
--   2. an all-1 fraction wraps to all-T and carry stops in the exponent;
--   3. all-1 fraction and exponent wrap and carry enters the regime.
------------------------------------------------------------------------

allPositive : (n : Nat) → Vec Trit.Trit n
allPositive zero = []
allPositive (suc n) = Trit.pos ∷ allPositive n

allNegative : (n : Nat) → Vec Trit.Trit n
allNegative zero = []
allNegative (suc n) = Trit.neg ∷ allNegative n

successorAllPositiveAppend :
  ∀ (p : Nat) {m} (tail : Vec Trit.Trit m) →
  Succ.successorWord (allPositive p ++ tail)
  ≡ allNegative p ++ Succ.successorWord tail
successorAllPositiveAppend zero tail = refl
successorAllPositiveAppend (suc p) tail =
  cong (Trit.neg ∷_) (successorAllPositiveAppend p tail)

successorStopsInPrefix :
  ∀ {p m} {prefix : Vec Trit.Trit p} {tail : Vec Trit.Trit m} →
  Succ.HasSuccessor prefix →
  Succ.successorWord (prefix ++ tail)
  ≡ Succ.successorWord prefix ++ tail
successorStopsInPrefix Succ.negativeHead = refl
successorStopsInPrefix Succ.zeroHead = refl
successorStopsInPrefix (Succ.positiveCarry carry) =
  cong (Trit.neg ∷_) (successorStopsInPrefix carry)

fractionCarryCase :
  ∀ {p e r}
  {fraction : Vec Trit.Trit p}
  {exponent : Vec Trit.Trit e}
  {regime : Vec Trit.Trit r} →
  Succ.HasSuccessor fraction →
  Succ.successorWord (fraction ++ exponent ++ regime)
  ≡ Succ.successorWord fraction ++ exponent ++ regime
fractionCarryCase carry = successorStopsInPrefix carry

exponentCarryCase :
  ∀ {p e r}
  (fractionWidth : Nat)
  {exponent : Vec Trit.Trit e}
  {regime : Vec Trit.Trit r} →
  p ≡ fractionWidth →
  Succ.HasSuccessor exponent →
  Succ.successorWord (allPositive p ++ exponent ++ regime)
  ≡ allNegative p ++ Succ.successorWord exponent ++ regime
exponentCarryCase {p} fractionWidth refl carry =
  trans
    (successorAllPositiveAppend p (_ ++ _))
    (cong (allNegative p ++_) (successorStopsInPrefix carry))

regimeCarryCase :
  ∀ {p e r}
  {regime : Vec Trit.Trit r} →
  Succ.HasSuccessor regime →
  Succ.successorWord (allPositive p ++ allPositive e ++ regime)
  ≡ allNegative p ++ allNegative e ++ Succ.successorWord regime
regimeCarryCase {p} {e} carry =
  trans
    (successorAllPositiveAppend p (allPositive e ++ _))
    (cong (allNegative p ++_) (successorAllPositiveAppend e _))
