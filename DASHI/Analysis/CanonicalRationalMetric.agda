module DASHI.Analysis.CanonicalRationalMetric where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base
  using (ℚ; 0ℚ; 1ℚ; ½; _+_; _-_; _*_; -_; ∣_∣; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚ
open import Data.Rational.Tactic.RingSolver using (solve-∀)

open import DASHI.Analysis.FastCauchyReals

------------------------------------------------------------------------
-- The standard library's reduced rational carrier supplies the exact metric
-- base for the rapidly convergent real construction.  The approximation radius
-- is genuinely dyadic: epsilon n = (1/2)^n.

dyadicQ : Nat → ℚ
dyadicQ zero = 1ℚ
dyadicQ (suc n) = ½ * dyadicQ n

subSelfℚ : ∀ q → q - q ≡ 0ℚ
subSelfℚ q = ℚ.+-inverseʳ q

absZeroℚ : ∣ 0ℚ ∣ ≡ 0ℚ
absZeroℚ = ℚ.0≤p⇒∣p∣≡p ℚ.≤-refl

differenceSymmetry : ∀ x y → x - y ≡ - (y - x)
differenceSymmetry = solve-∀

absDifferenceSymmetry : ∀ x y → ∣ x - y ∣ ≡ ∣ y - x ∣
absDifferenceSymmetry x y
  rewrite differenceSymmetry x y =
  ℚ.∣-p∣≡∣p∣ (y - x)

differenceSplit : ∀ x y z → x - z ≡ (x - y) + (y - z)
differenceSplit = solve-∀

absDifferenceTriangle : ∀ x y z →
  ∣ x - z ∣ ≤ ∣ x - y ∣ + ∣ y - z ∣
absDifferenceTriangle x y z
  rewrite differenceSplit x y z =
  ℚ.∣p+q∣≤∣p∣+∣q∣ (x - y) (y - z)

halfNonnegative : 0ℚ ≤ ½
halfNonnegative = ℚ.0≤∣p∣ ½

oneNonnegative : 0ℚ ≤ 1ℚ
oneNonnegative = ℚ.0≤∣p∣ 1ℚ

dyadicQNonnegative : ∀ n → 0ℚ ≤ dyadicQ n
dyadicQNonnegative zero = oneNonnegative
dyadicQNonnegative (suc n) =
  ℚ.nonNegative⁻¹ (½ * dyadicQ n)
  where
    instance
      halfNN : NonNegative ½
      halfNN = nonNegative halfNonnegative

      tailNN : NonNegative (dyadicQ n)
      tailNN = nonNegative (dyadicQNonnegative n)

zeroBelowDyadicQSum : ∀ m n → 0ℚ ≤ dyadicQ m + dyadicQ n
zeroBelowDyadicQSum m n = begin
  0ℚ                 ≡⟨ ℚ.+-identityˡ 0ℚ ⟨
  0ℚ + 0ℚ            ≤⟨ ℚ.+-mono-≤ (dyadicQNonnegative m) (dyadicQNonnegative n) ⟩
  dyadicQ m + dyadicQ n ∎
  where open ℚ.≤-Reasoning

canonicalRationalMetricAuthority : RationalMetricAuthority
canonicalRationalMetricAuthority =
  record
    { Q = ℚ
    ; zeroQ = 0ℚ
    ; oneQ = 1ℚ
    ; _+Q_ = _+_
    ; _-Q_ = _-_
    ; _*Q_ = _*_
    ; negQ = -_
    ; absQ = ∣_∣
    ; _≤Q_ = _≤_
    ; dyadicError = dyadicQ
    ; leRefl = λ q → ℚ.≤-refl
    ; leTrans = ℚ.≤-trans
    ; addMono = ℚ.+-mono-≤
    ; subSelfQ = subSelfℚ
    ; absZero = absZeroℚ
    ; absSymmetricDifference = absDifferenceSymmetry
    ; absTriangleDifference = absDifferenceTriangle
    ; dyadicPositive = dyadicQNonnegative
    ; zeroBelowDyadicSum = zeroBelowDyadicQSum
    }

canonicalRationalEmbedding : ℚ → FastCauchyReal canonicalRationalMetricAuthority
canonicalRationalEmbedding = constantFastReal canonicalRationalMetricAuthority
