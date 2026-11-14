module DASHI.Mathematics.Automorphic.EllipticCMLevel32LigozatCuspArithmeticExact where

------------------------------------------------------------------------
-- ACTUAL LEVEL-32 η(4τ)²η(8τ)² CUSP-ORDER ARITHMETIC.
--
-- Ligozat's formula for eta quotients gives:
--
--   v_d(f) = N / (24*d*gcd(d,N/d))
--             * sum_{δ|N} r_δ gcd(d,δ)^2/δ.
--
-- N=32, r4=r8=2. For the six divisor denominators
-- d=1,2,4,8,16,32 all cusp orders are EXACTLY ONE.
--
-- Multiplying the desired identity v_d=1 by 24*d*gcd*8:
--   24*d*gcd(d,32/d)*8
--     = 32*(4*gcd(d,4)^2 + 2*gcd(d,8)^2).
--
-- All actual gcd labels, divisor products, and equalities
-- are proved by normalization (refl) on concrete Nat values.
-- This pays the REAL finite eta-cusp arithmetic, not an
-- assumed "cusp positive" Boolean.
--
-- It does NOT formalize Ligozat's analytic eta-quotient
-- theorem, modular character, cusp parameter or Bishop eta
-- convergence. Those are separate K4 same-object proofs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat.GCD using (gcd)
open import Agda.Builtin.List using (List; []; _∷_)

record Level32CuspArithmetic : Set where
  constructor level32-cusp
  field
    denominator dualDenominator : Nat
    denominatorDividesLevel :
      denominator * dualDenominator ≡ 32
    widthGcd : Nat
    widthGcdActual :
      gcd denominator dualDenominator ≡ widthGcd
    gcdFour gcdEight : Nat
    gcdFourActual : gcd denominator 4 ≡ gcdFour
    gcdEightActual : gcd denominator 8 ≡ gcdEight

    -- Exactly Ligozat order 1, denominator cleared.
    ligozatOrderOneCrossMultiplied :
      (24 * denominator * widthGcd) * 8
      ≡ 32 *
          (4 * gcdFour * gcdFour
           + 2 * gcdEight * gcdEight)

open Level32CuspArithmetic public

cuspOne : Level32CuspArithmetic
cuspOne = level32-cusp
  1 32 refl
  1 refl
  1 1 refl refl
  refl

cuspTwo : Level32CuspArithmetic
cuspTwo = level32-cusp
  2 16 refl
  2 refl
  2 2 refl refl
  refl

cuspFour : Level32CuspArithmetic
cuspFour = level32-cusp
  4 8 refl
  4 refl
  4 4 refl refl
  refl

cuspEight : Level32CuspArithmetic
cuspEight = level32-cusp
  8 4 refl
  4 refl
  4 8 refl refl
  refl

cuspSixteen : Level32CuspArithmetic
cuspSixteen = level32-cusp
  16 2 refl
  2 refl
  4 8 refl refl
  refl

cuspThirtyTwo : Level32CuspArithmetic
cuspThirtyTwo = level32-cusp
  32 1 refl
  1 refl
  4 8 refl refl
  refl

-- All six divisor denominators, covering all eight cusps
-- because denominator 4 and 8 each have two numerator orbits.
level32CuspDenominatorWitnesses : List Level32CuspArithmetic
level32CuspDenominatorWitnesses =
  cuspOne ∷ cuspTwo ∷ cuspFour
    ∷ cuspEight ∷ cuspSixteen ∷ cuspThirtyTwo ∷ []

-- A finite proof-carrying transfer from our exact gcd/order
-- identities to the analytical Ligozat order-one result needs
-- the original Ligozat theorem as a separate mathematical owner.
-- This record is a FINITE arithmetic certificate only.
level32CuspOneWitness :
  (cusp : Level32CuspArithmetic) →
  (24 * denominator cusp * widthGcd cusp) * 8
  ≡ 32 *
      (4 * gcdFour cusp * gcdFour cusp
       + 2 * gcdEight cusp * gcdEight cusp)
level32CuspOneWitness = ligozatOrderOneCrossMultiplied
