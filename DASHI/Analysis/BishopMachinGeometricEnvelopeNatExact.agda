module DASHI.Analysis.BishopMachinGeometricEnvelopeNatExact where

------------------------------------------------------------------------
-- K04b2 exact all-Nat cross-multiplied Machin alternating envelope.
-- Machin's (1706) formula and classical alternating-series remainder.
--
-- For n>=0:
-- e_n = 16/((2n+1)*5*25^n) + 4/((2n+1)*239*57121^n).
-- The statement e_n <= 4/25^n, after multiplying strictly positive
-- denominators and cancelling 25^n, reduces EXACTLY to:
--
-- 3824*57121^n + 20*25^n <= (2n+1)*4780*57121^n.
--
-- This file proves that natural inequality uniformly by arithmetic
-- monotonicity, rather than sampling finite n or appealing to a
-- synthetic analytic bound. Remaining: rational denominator/cancel
-- transport and embedding into the actual Bishop real-order bound.
-- Source-written; Agda kernel check pending.
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _^_; _≤_)
import Data.Nat.Properties as P
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

pow25 pow57121 : ℕ → ℕ
pow25 n = 25 ^ n
pow57121 n = 57121 ^ n

twentyFiveBelow57121 : 25 ≤ 57121
twentyFiveBelow57121 = P.m≤m+n 25 57096

pow25BelowPow57121 : ∀ n → pow25 n ≤ pow57121 n
pow25BelowPow57121 zero = P.≤-refl
pow25BelowPow57121 (suc n) =
  P.*-mono-≤ twentyFiveBelow57121 (pow25BelowPow57121 n)

coefficientBelow : 3844 ≤ 4780
coefficientBelow = P.m≤m+n 3844 936

-- 16*239 = 3824, 4*5 = 20, 4*5*239 = 4780.
-- The first coefficient and the RHS target are literal arithmetic;
-- no extra postulates or proof by checked finite examples.
combinedNumeratorBelowBase : ∀ n →
  3824 * pow57121 n + 20 * pow25 n
    ≤ 4780 * pow57121 n
combinedNumeratorBelowBase n =
  P.≤-trans
    (P.+-mono-≤ P.≤-refl
      (P.*-mono-≤ P.≤-refl (pow25BelowPow57121 n)))
    (subst
      (λ x → x ≤ 4780 * pow57121 n)
      (sym (P.*-distribʳ-+ (pow57121 n) 3824 20))
      (P.*-mono-≤ coefficientBelow P.≤-refl))

-- Multiplication by the odd denominator (2n+1) can only enlarge
-- the right side; the expansion is definitional for Nat multiplication.
baseBelowOddMultiple : ∀ n →
  4780 * pow57121 n
    ≤ suc (2 * n) * (4780 * pow57121 n)
baseBelowOddMultiple n =
  P.m≤m+n
    (4780 * pow57121 n)
    ((2 * n) * (4780 * pow57121 n))

-- This is the complete closed-form Nat inequality equivalent
-- to the desired rational remainder bound after positive-denominator
-- normalization. It is meaningful for n=0 as well as n>=1.
machinGeometricEnvelopeCrossMultiplied : ∀ n →
  3824 * pow57121 n + 20 * pow25 n
    ≤ suc (2 * n) * (4780 * pow57121 n)
machinGeometricEnvelopeCrossMultiplied n =
  P.≤-trans
    (combinedNumeratorBelowBase n)
    (baseBelowOddMultiple n)
