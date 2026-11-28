module DASHI.Moonshine.JInvariantThetaIntegerTwistExact where

-- Source-written, kernel pending. Sign and monomial transport on the
-- original integer Cauchy row, using its existing head recurrence.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -_; _+_; _*_)
import Data.Integer.Properties as Z
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Moonshine.JInvariantThetaLegendreSignedGeometryExact as T

open I using (SeriesZ; rowZ; rowHead; rowZero)

shift : SeriesZ → SeriesZ
shift f n = f (suc n)

twist : SeriesZ → SeriesZ
twist f n = T.sign n * f n

scale : ℤ → SeriesZ → SeriesZ
scale c f n = c * f n

rowCong : ∀ f g u v → (∀ n → f n ≡ u n) → (∀ n → g n ≡ v n) →
  ∀ n → rowZ f g n ≡ rowZ u v n
rowCong f g u v hf hg zero =
  trans (rowZero f g) (trans (cong₂ _*_ (hf zero) (hg zero)) (sym (rowZero u v)))
rowCong f g u v hf hg (suc n) =
  trans (rowHead f g n)
    (trans (cong₂ _+_ (cong₂ _*_ (hf zero) (hg (suc n)))
      (rowCong (shift f) g (shift u) v (λ k → hf (suc k)) hg n))
      (sym (rowHead u v n)))

rowScale : ∀ c f g n → rowZ (scale c f) g n ≡ c * rowZ f g n
rowScale c f g zero = trans (rowZero (scale c f) g)
  (trans (Z.*-assoc c (f zero) (g zero)) (cong (c *_) (sym (rowZero f g))))
rowScale c f g (suc n) = trans (rowHead (scale c f) g n)
  (trans (cong₂ _+_ (Z.*-assoc c (f zero) (g (suc n))) (rowScale c (shift f) g n))
    (trans (sym (Z.*-distribˡ-+ c (f zero * g (suc n)) (rowZ (shift f) g n)))
      (cong (c *_) (sym (rowHead f g n)))))

signStep : ∀ n → T.sign (suc n) ≡ (- (+ 1)) * T.sign n
signStep n = sym (solve 1 (λ x → con (- (+ 1)) :* x := con (+ 0) :- x) refl (T.sign n))

shiftTwist : ∀ f n → shift (twist f) n ≡ scale (- (+ 1)) (twist (shift f)) n
shiftTwist f n = trans (cong (_* f (suc n)) (signStep n))
  (Z.*-assoc (- (+ 1)) (T.sign n) (f (suc n)))

rowTwist : ∀ f g n → rowZ (twist f) (twist g) n ≡ twist (rowZ f g) n
rowTwist f g zero = trans (rowZero (twist f) (twist g))
  (trans (solve 2 (λ a b → (con (+ 1) :* a) :* (con (+ 1) :* b) := con (+ 1) :* (a :* b)) refl (f zero) (g zero))
    (cong ((+ 1) *_) (sym (rowZero f g))))
rowTwist f g (suc n) =
  let s = T.sign (suc n)
      tail = rowZ (shift f) g n
      step : rowZ (shift (twist f)) (twist g) n ≡ s * tail
      step = trans (rowCong (shift (twist f)) (twist g)
        (scale (- (+ 1)) (twist (shift f))) (twist g) (shiftTwist f) (λ _ → refl) n)
        (trans (rowScale (- (+ 1)) (twist (shift f)) (twist g) n)
          (trans (cong ((- (+ 1)) *_) (rowTwist (shift f) g n))
            (trans (sym (Z.*-assoc (- (+ 1)) (T.sign n) tail))
              (cong (_* tail) (sym (signStep n))))))
  in trans (rowHead (twist f) (twist g) n)
    (trans (cong₂ _+_ (solve 3 (λ s a b → (con (+ 1) :* a) :* (s :* b) := s :* (a :* b))
      refl s (f zero) (g (suc n))) step)
      (trans (sym (Z.*-distribˡ-+ s (f zero * g (suc n)) tail))
        (cong (s *_) (sym (rowHead f g n)))))

fourthTwist : ∀ f n → T.fourth (twist f) n ≡ twist (T.fourth f) n
fourthTwist f n = trans
  (rowCong (rowZ (twist f) (twist f)) (rowZ (twist f) (twist f))
    (twist (rowZ f f)) (twist (rowZ f f)) (rowTwist f f) (rowTwist f f) n)
  (rowTwist (rowZ f f) (rowZ f f) n)

negativeSheet : ∀ n → T.C n ≡ twist T.B n
negativeSheet = fourthTwist T.theta3

zeroZ unitZ mono16 : SeriesZ
zeroZ n = + 0
unitZ zero = + 1
unitZ (suc n) = + 0
mono16 zero = + 0
mono16 (suc zero) = + 16
mono16 (suc (suc n)) = + 0

rowZeroLeft : ∀ f n → rowZ zeroZ f n ≡ + 0
rowZeroLeft f zero = trans (rowZero zeroZ f) (Z.*-zeroˡ (f zero))
rowZeroLeft f (suc n) = trans (rowHead zeroZ f n)
  (trans (cong₂ _+_ (Z.*-zeroˡ (f (suc n))) (rowZeroLeft f n)) refl)

rowUnitLeft : ∀ f n → rowZ unitZ f n ≡ f n
rowUnitLeft f zero = trans (rowZero unitZ f) (Z.*-identityˡ (f zero))
rowUnitLeft f (suc n) = trans (rowHead unitZ f n)
  (trans (cong₂ _+_ (Z.*-identityˡ (f (suc n))) (rowZeroLeft f n))
    (Z.+-identityʳ (f (suc n))))

monoRead : ∀ f n → rowZ mono16 f (suc n) ≡ (+ 16) * f n
monoRead f n = trans (rowHead mono16 f n)
  (trans (cong₂ _+_ (Z.*-zeroˡ (f (suc n)))
    (trans (rowCong (shift mono16) f (scale (+ 16) unitZ) f
      (λ { zero → refl ; (suc k) → refl }) (λ _ → refl) n)
      (trans (rowScale (+ 16) unitZ f n) (cong ((+ 16) *_) (rowUnitLeft f n)))))
    (Z.+-identityˡ ((+ 16) * f n)))

aRead : ∀ n → rowZ mono16 (T.fourth T.halfTheta) n ≡ T.A n
aRead zero = trans (rowZero mono16 (T.fourth T.halfTheta)) (Z.*-zeroˡ _)
aRead (suc n) = monoRead (T.fourth T.halfTheta) n
