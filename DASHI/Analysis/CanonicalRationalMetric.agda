module DASHI.Analysis.CanonicalRationalMetric where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Rational.Base
  using (ℚ; 0ℚ; 1ℚ; ½; _+_; _-_; _*_; -_; ∣_∣; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚ
open import Data.Rational.Tactic.RingSolver using (solve-∀)

open import DASHI.Analysis.FastCauchyReals
open import DASHI.Analysis.FastCauchyArithmetic

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
  0ℚ                    ≡⟨ ℚ.+-identityˡ 0ℚ ⟨
  0ℚ + 0ℚ               ≤⟨ ℚ.+-mono-≤ (dyadicQNonnegative m) (dyadicQNonnegative n) ⟩
  dyadicQ m + dyadicQ n ∎
  where open ℚ.≤-Reasoning

halfDouble : ∀ q → (½ * q) + (½ * q) ≡ q
halfDouble = solve-∀

dyadicDoubleStepℚ : ∀ n →
  dyadicQ (suc n) + dyadicQ (suc n) ≡ dyadicQ n
dyadicDoubleStepℚ n = halfDouble (dyadicQ n)

dyadicOneStep : ∀ n → dyadicQ (suc n) ≤ dyadicQ n
dyadicOneStep n = begin
  dyadicQ (suc n)
    ≡⟨ ℚ.+-identityʳ (dyadicQ (suc n)) ⟨
  dyadicQ (suc n) + 0ℚ
    ≤⟨ ℚ.+-mono-≤ ℚ.≤-refl (dyadicQNonnegative (suc n)) ⟩
  dyadicQ (suc n) + dyadicQ (suc n)
    ≡⟨ dyadicDoubleStepℚ n ⟩
  dyadicQ n ∎
  where open ℚ.≤-Reasoning

dyadicBelowOne : ∀ n → dyadicQ n ≤ 1ℚ
dyadicBelowOne zero = ℚ.≤-refl
dyadicBelowOne (suc n) =
  ℚ.≤-trans (dyadicOneStep n) (dyadicBelowOne n)

dyadicAntitoneℚ : ∀ {m n} → m ≤ n → dyadicQ n ≤ dyadicQ m
dyadicAntitoneℚ {zero} {n} z≤n = dyadicBelowOne n
dyadicAntitoneℚ {suc m} {suc n} (s≤s m≤n) =
  ℚ.*-monoˡ-≤-nonNeg ½ (dyadicAntitoneℚ m≤n)
  where
    instance
      halfNN : NonNegative ½
      halfNN = nonNegative halfNonnegative

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
    ; leRefl = λ _ → ℚ.≤-refl
    ; leTrans = ℚ.≤-trans
    ; addMono = ℚ.+-mono-≤
    ; subSelfQ = subSelfℚ
    ; absZero = absZeroℚ
    ; absSymmetricDifference = absDifferenceSymmetry
    ; absTriangleDifference = absDifferenceTriangle
    ; dyadicPositive = dyadicQNonnegative
    ; zeroBelowDyadicSum = zeroBelowDyadicQSum
    ; dyadicAntitone = dyadicAntitoneℚ
    ; dyadicDoubleStep = dyadicDoubleStepℚ
    }

canonicalRationalEmbedding : ℚ → FastCauchyReal canonicalRationalMetricAuthority
canonicalRationalEmbedding = constantFastReal canonicalRationalMetricAuthority

------------------------------------------------------------------------
-- Exact additive laws used by precision-safe representative arithmetic.

negDifference : ∀ a b → (- a) - (- b) ≡ - (a - b)
negDifference = solve-∀

negDifferenceAbsℚ : ∀ a b → ∣ (- a) - (- b) ∣ ≡ ∣ a - b ∣
negDifferenceAbsℚ a b
  rewrite negDifference a b =
  ℚ.∣-p∣≡∣p∣ (a - b)

addDifference : ∀ a b c d →
  (a + b) - (c + d) ≡ (a - c) + (b - d)
addDifference = solve-∀

addDifferenceBoundℚ : ∀ a b c d →
  ∣ (a + b) - (c + d) ∣ ≤ ∣ a - c ∣ + ∣ b - d ∣
addDifferenceBoundℚ a b c d
  rewrite addDifference a b c d =
  ℚ.∣p+q∣≤∣p∣+∣q∣ (a - c) (b - d)

doublePairDyadic : ∀ m n →
  (dyadicQ (suc m) + dyadicQ (suc n))
    + (dyadicQ (suc m) + dyadicQ (suc n))
  ≡ dyadicQ m + dyadicQ n
doublePairDyadic m n = solve-∀

canonicalFastCauchyAdditiveLaws :
  FastCauchyAdditiveLaws canonicalRationalMetricAuthority
canonicalFastCauchyAdditiveLaws =
  record
    { negDifferenceAbs = negDifferenceAbsℚ
    ; addDifferenceBound = addDifferenceBoundℚ
    ; doublePairError = doublePairDyadic
    }

canonicalFastZero canonicalFastOne :
  FastCauchyReal canonicalRationalMetricAuthority
canonicalFastZero = canonicalRationalEmbedding 0ℚ
canonicalFastOne = canonicalRationalEmbedding 1ℚ

canonicalFastNeg :
  FastCauchyReal canonicalRationalMetricAuthority →
  FastCauchyReal canonicalRationalMetricAuthority
canonicalFastNeg = fastNeg canonicalFastCauchyAdditiveLaws

canonicalFastAdd :
  FastCauchyReal canonicalRationalMetricAuthority →
  FastCauchyReal canonicalRationalMetricAuthority →
  FastCauchyReal canonicalRationalMetricAuthority
canonicalFastAdd = fastAdd canonicalFastCauchyAdditiveLaws

canonicalFastSub :
  FastCauchyReal canonicalRationalMetricAuthority →
  FastCauchyReal canonicalRationalMetricAuthority →
  FastCauchyReal canonicalRationalMetricAuthority
canonicalFastSub = fastSub canonicalFastCauchyAdditiveLaws
