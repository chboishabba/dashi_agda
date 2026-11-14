module DASHI.Mathematics.Arithmetic.EllipticOddPrimeSecondValuationParityExact where

------------------------------------------------------------------------
-- BSD K1 second ORIGINAL x-T coordinate: [x-1] on y²=x(x-1)(x+1).
--
-- For any odd prime p and actual nonexceptional E(Q_p) point,
-- s = v_p(x-1) falls into three cases:
--   s > 0: x and x+1 are p-adic units (p odd), so 2v_p(y)=s.
--   s = 0: parity is immediate.
--   s < 0: x and x+1 have valuation s, so 2v_p(y)=3s.
-- Thus s is EVEN for ALL ODD primes, not necessarily at 2.
-- At p=2, (1,0) has original torsion Kummer second class [2],
-- so a universal second-2-adic-parity theorem would be false.
--
-- Source theorem is the literal integer case algebra; Q_p local
-- point, ultrametric/henselian valuation, H¹(E[2]) local Kummer map
-- and global support/faithfulness are separate unpaid K1 owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer using (ℤ; +_; _*_)
import DASHI.Mathematics.Arithmetic.EllipticCubicValuationParityExact as Parity

data OddPrimeSecondCoordinateRegime
    (secondValuation yValuation : ℤ) : Set where
  secondUnit :
    secondValuation ≡ (+ 0) →
    OddPrimeSecondCoordinateRegime secondValuation yValuation
  secondCloseToOne :
    ((+ 2) * yValuation) ≡ secondValuation →
    OddPrimeSecondCoordinateRegime secondValuation yValuation
  secondPole :
    ((+ 2) * yValuation) ≡ ((+ 3) * secondValuation) →
    OddPrimeSecondCoordinateRegime secondValuation yValuation

originalOddPrimeSecondCoordinateEven :
  (secondValuation yValuation : ℤ) →
  OddPrimeSecondCoordinateRegime secondValuation yValuation →
  Parity.EvenValuation secondValuation
originalOddPrimeSecondCoordinateEven secondValuation yValuation
    (secondUnit h) =
  Parity.unitValuationEven secondValuation h
originalOddPrimeSecondCoordinateEven secondValuation yValuation
    (secondCloseToOne h) =
  Parity.positiveValuationBalanceEven
    secondValuation yValuation h
originalOddPrimeSecondCoordinateEven secondValuation yValuation
    (secondPole h) =
  Parity.negativeValuationBalanceEven
    secondValuation yValuation h
