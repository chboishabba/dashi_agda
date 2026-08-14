module DASHI.Physics.YangMills.BalabanP33RationalQuaternionCoreExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Relation.Binary.PropositionalEquality using (cong)

record RationalQuaternion : Set where
  constructor quat
  field
    q0 q1 q2 q3 : ℚ

open RationalQuaternion public

zeroQ oneQ : RationalQuaternion
zeroQ = quat 0ℚ 0ℚ 0ℚ 0ℚ
oneQ = quat 1ℚ 0ℚ 0ℚ 0ℚ

_+q_ : RationalQuaternion → RationalQuaternion → RationalQuaternion
quat a0 a1 a2 a3 +q quat b0 b1 b2 b3 =
  quat (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3)

negQ : RationalQuaternion → RationalQuaternion
negQ (quat a0 a1 a2 a3) = quat (- a0) (- a1) (- a2) (- a3)

_*q_ : RationalQuaternion → RationalQuaternion → RationalQuaternion
quat a0 a1 a2 a3 *q quat b0 b1 b2 b3 =
  quat
    (a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3)
    (a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2)
    (a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1)
    (a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0)

quaternionExt :
  ∀ {left right} →
  q0 left ≡ q0 right → q1 left ≡ q1 right →
  q2 left ≡ q2 right → q3 left ≡ q3 right →
  left ≡ right
quaternionExt {quat _ _ _ _} {quat _ _ _ _} refl refl refl refl = refl

q0Multiply : ∀ a b →
  q0 (a *q b) ≡ q0 a * q0 b - q1 a * q1 b - q2 a * q2 b - q3 a * q3 b
q0Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) = refl

q1Multiply : ∀ a b →
  q1 (a *q b) ≡ q0 a * q1 b + q1 a * q0 b + q2 a * q3 b - q3 a * q2 b
q1Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) = refl

q2Multiply : ∀ a b →
  q2 (a *q b) ≡ q0 a * q2 b - q1 a * q3 b + q2 a * q0 b + q3 a * q1 b
q2Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) = refl

q3Multiply : ∀ a b →
  q3 (a *q b) ≡ q0 a * q3 b + q1 a * q2 b - q2 a * q1 b + q3 a * q0 b
q3Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) = refl

q0Add : ∀ a b → q0 (a +q b) ≡ q0 a + q0 b
q0Add (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) = refl
q1Add : ∀ a b → q1 (a +q b) ≡ q1 a + q1 b
q1Add (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) = refl
q2Add : ∀ a b → q2 (a +q b) ≡ q2 a + q2 b
q2Add (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) = refl
q3Add : ∀ a b → q3 (a +q b) ≡ q3 a + q3 b
q3Add (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) = refl
