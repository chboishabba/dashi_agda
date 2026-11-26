module DASHI.Moonshine.JInvariantBishopEulerDefectUniquenessExact where

-- SOURCE-WRITTEN, UNCOMPILED. Same original finite Cauchy row.
-- Generalize the existing positive-degree triangular uniqueness proof
-- to an Euler defect with a positive leading cusp coefficient.
-- No independent formal root and no division by q.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (refl)
open import Data.Nat.Base using (_≤_; z≤n)
import Data.Nat.Properties as NP
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import Real as R
open R using (ℝ; _≃_; _+_; _*_; _⋆)
import RealProperties as P
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as C
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as N
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
open U using (Series; _⊗s_; D; PrefixEq; convPrefix; zeroHead; right0; add0)

operator : Nat → Series → Series → Series → Series → Series
operator d a b c f n =
  (a ⊗s D d f) n + (b ⊗s D 1 f) n + (c ⊗s f) n

positiveNat : (n : Nat) → R.Positive (NR.natReal (suc n))
positiveNat n = P.posp⇒posp⋆ (+ (suc n) / 1) (QP.positive⁻¹ (+ (suc n) / 1))

positivePower : (x : ℝ) → R.Positive x → (d : Nat) → R.Positive (R.pow x d)
positivePower x px zero = P.posp⇒posp⋆ Q.1ℚᵘ (QP.positive⁻¹ Q.1ℚᵘ)
positivePower x px (suc d) = P.posx,y⇒posx*y (positivePower x px d) px

zeroTail : (a f : Series) (d n : Nat) →
  PrefixEq f H.zeroSeries n → (a ⊗s D d f) n ≃ R.0ℝ
zeroTail a f d n h = P.≃-trans
  (convPrefix a (D d f) H.zeroSeries n (λ k hk → right0 (h k hk)))
  (H.zeroRow a n)

zeroTailPlain : (a f : Series) (n : Nat) →
  PrefixEq f H.zeroSeries n → (a ⊗s f) n ≃ R.0ℝ
zeroTailPlain a f n h = P.≃-trans
  (convPrefix a f H.zeroSeries n h) (H.zeroRow a n)

lead : Nat → Series → Nat → ℝ
lead d a n = a zero * R.pow (NR.natReal n) d

leadPositive : (d : Nat) (a : Series) → R.Positive (a zero) →
  (n : Nat) → R.Positive (lead d a (suc n))
leadPositive d a pa n =
  P.posx,y⇒posx*y pa (positivePower (NR.natReal (suc n)) (positiveNat n) d)

headOnZeroPrefix : (d : Nat) (a f : Series) (n : Nat) →
  PrefixEq f H.zeroSeries n →
  (a ⊗s D d f) (suc n) ≃ lead d a (suc n) * f (suc n)
headOnZeroPrefix d a f n h =
  P.≃-trans (C.cauchyCoefficientSuccessor a (D d f) n)
    (P.≃-trans
      (P.+-cong
        (P.≃-symm (P.*-assoc (a zero) (R.pow (NR.natReal (suc n)) d) (f (suc n))))
        (zeroTail (C.shift a) f d n h))
      (P.+-identityʳ (lead d a (suc n) * f (suc n))))

operatorOnZeroPrefix : (d : Nat) (a b c f : Series) →
  b zero ≃ R.0ℝ → c zero ≃ R.0ℝ → (n : Nat) →
  PrefixEq f H.zeroSeries n →
  operator d a b c f (suc n) ≃ lead d a (suc n) * f (suc n)
operatorOnZeroPrefix d a b c f hb hc n h =
  let v = lead d a (suc n) * f (suc n) in
  P.≃-trans
    (P.+-cong (P.+-cong (headOnZeroPrefix d a f n h)
      (P.≃-trans (zeroHead b (D 1 f) hb n) (zeroTail (C.shift b) f 1 n h)))
      (P.≃-trans (zeroHead c f hc n) (zeroTailPlain (C.shift c) f n h)))
    (P.≃-trans (P.+-cong (P.+-identityʳ v) P.≃-refl) (P.+-identityʳ v))

nextZero : (d : Nat) (a b c f : Series) →
  R.Positive (a zero) → b zero ≃ R.0ℝ → c zero ≃ R.0ℝ →
  (∀ n → operator d a b c f n ≃ R.0ℝ) →
  (n : Nat) → PrefixEq f H.zeroSeries n → f (suc n) ≃ R.0ℝ
nextZero d a b c f pa hb hc hr n h =
  N.cancelLeft (lead d a (suc n)) (leadPositive d a pa n)
    (P.≃-trans (P.≃-symm (operatorOnZeroPrefix d a b c f hb hc n h))
      (P.≃-trans (hr (suc n)) (P.≃-symm (P.*-zeroʳ (lead d a (suc n))))))

prefixZero : (d : Nat) (a b c f : Series) →
  R.Positive (a zero) → b zero ≃ R.0ℝ → c zero ≃ R.0ℝ →
  (∀ n → operator d a b c f n ≃ R.0ℝ) →
  f zero ≃ R.0ℝ → (n : Nat) → PrefixEq f H.zeroSeries n
prefixZero d a b c f pa hb hc hr hz zero zero hk = hz
prefixZero d a b c f pa hb hc hr hz zero (suc k) ()
prefixZero d a b c f pa hb hc hr hz (suc n) k hk with k NP.≟ suc n
... | yes refl = nextZero d a b c f pa hb hc hr n
  (prefixZero d a b c f pa hb hc hr hz n)
... | no neq = prefixZero d a b c f pa hb hc hr hz n k
  (NP.≤-pred (NP.≤∧≢⇒< hk neq))

allZero : (d : Nat) (a b c f : Series) →
  R.Positive (a zero) → b zero ≃ R.0ℝ → c zero ≃ R.0ℝ →
  (∀ n → operator d a b c f n ≃ R.0ℝ) →
  f zero ≃ R.0ℝ → (n : Nat) → f n ≃ R.0ℝ
allZero d a b c f pa hb hc hr hz n =
  prefixZero d a b c f pa hb hc hr hz n n NP.≤-refl
