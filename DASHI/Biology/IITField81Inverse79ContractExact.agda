module DASHI.Biology.IITField81Inverse79ContractExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (sym; trans)

------------------------------------------------------------------------
-- Explicit finite-field multiplicative contract for 3^4 = 81.
-- This module does NOT assert field axioms merely from 81-element count.
-- Given the concrete field multiplication and Fermat a^80=one, its
-- algebraic inverse-79 conclusion is constructive, not a numeric slogan.
--
-- Source targets:
--   iit_jfine_selected_punctured79_audit.py (concrete quartic F81)
--   IITProjectiveF9Pointed80Exact (finite quotient sources)
--   RiemannQuarticPuncturedKernel4EnumerationExact (actual 80 puncture)
-- Compiler receipt: pending.
------------------------------------------------------------------------

record Field81MultiplicativeLaws (K : Set) : Set₁ where
  field
    one : K
    multiply : K → K → K
    power : K → Nat → K
    isNonzero : K → Set
    powerZero : ∀ a → power a 0 ≡ one
    powerSucc : ∀ a n →
      power a (suc n) ≡ multiply a (power a n)
    multiplyAssociative : ∀ a b c →
      multiply (multiply a b) c ≡ multiply a (multiply b c)
    multiplyRightUnit : ∀ a → multiply a one ≡ a
    nonzeroFermat80 : ∀ a → isNonzero a → power a 80 ≡ one

open Field81MultiplicativeLaws public

-- Because power is recursively left-associated through powerSucc,
-- the defining equation suffices to show a *left* inverse after one
-- explicit multiplication. No commutativity postulate is needed here.
inverse79Left :
  ∀ {K} (laws : Field81MultiplicativeLaws K)
    (a : K) (nonzero : isNonzero laws a) →
  multiply laws a (power laws a 79) ≡ one laws
inverse79Left laws a nz =
  trans
    (sym (powerSucc laws a 79))
    (nonzeroFermat80 laws a nz)

record Field81ArithmeticBoundary : Set where
  constructor field81ArithmeticBoundary
  field
    eightyOneIsThreePowerFour : 3 * 3 * 3 * 3 ≡ 81
    unitOrderIsEighty : 81 - 1 ≡ 80
    inverseExponentIsSeventyNine : 81 - (3 - 1) ≡ 79
    directConcreteQuarticFieldAxiomsKernelProved : Bool
    actualPuncturedKernel4MultiplicationTransportKernelProved : Bool

canonicalField81ArithmeticBoundary : Field81ArithmeticBoundary
canonicalField81ArithmeticBoundary =
  field81ArithmeticBoundary refl refl refl false false
