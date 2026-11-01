module DASHI.ComputerScience.TekumFractionRangeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Integer.Base as ℤ using (+_; -_; _≤_)
open import Data.Nat.Base using (_<_)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.Algebra.BalancedTernaryCenteredReconstructionExact as Centered

------------------------------------------------------------------------
-- Exact integer range behind Hunhold's fraction inequality.
--
-- If F has p balanced trits, then
--
--   -A_p <= I_p(F) <= A_p,
--   2 A_p + 1 = 3^p,
--
-- hence the normalized fraction I_p(F)/3^p lies strictly between -1/2 and
-- +1/2.  This owner pays the integer part of that statement; the following
-- rational owner can transport it through Data.Rational without rebuilding
-- balanced positional arithmetic.
------------------------------------------------------------------------

fractionIntegerLower :
  ∀ {p} (fraction : Vec Trit.Trit p) →
  - (+ (Positional.center p)) ≤ BT.toInteger (BT.eval fraction)
fractionIntegerLower {p} fraction =
  subst
    (λ z → - (+ (Positional.center p)) ≤ z)
    (Centered.centeredValueEncode fraction)
    (Centered.centeredValueLower (Centered.encodeCentered fraction))

fractionIntegerUpper :
  ∀ {p} (fraction : Vec Trit.Trit p) →
  BT.toInteger (BT.eval fraction) ≤ + (Positional.center p)
fractionIntegerUpper {p} fraction =
  subst
    (λ z → z ≤ + (Positional.center p))
    (Centered.centeredValueEncode fraction)
    (Centered.centeredValueUpper (Centered.encodeCentered fraction))

fractionIntegerRange :
  ∀ {p} (fraction : Vec Trit.Trit p) →
  (- (+ (Positional.center p)) ≤ BT.toInteger (BT.eval fraction))
  × (BT.toInteger (BT.eval fraction) ≤ + (Positional.center p))
fractionIntegerRange fraction =
  fractionIntegerLower fraction , fractionIntegerUpper fraction

twiceCenterPlusOneIsPowerThree :
  (p : Nat) →
  2 * Positional.center p + 1 ≡ BT.pow3 p
twiceCenterPlusOneIsPowerThree = Centered.twiceCenterPlusOne

twiceCenterStrictlyBelowPowerThree :
  (p : Nat) →
  2 * Positional.center p < BT.pow3 p
twiceCenterStrictlyBelowPowerThree p =
  subst
    (λ bound → 2 * Positional.center p < bound)
    (twiceCenterPlusOneIsPowerThree p)
    NatP.≤-refl
