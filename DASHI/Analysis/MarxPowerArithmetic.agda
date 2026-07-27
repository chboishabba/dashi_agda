module DASHI.Analysis.MarxPowerArithmetic where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Set₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxPolynomialDifferential
open import DASHI.Analysis.MarxPowerRuleNormalisation

------------------------------------------------------------------------
-- The closed-form power rule uses a small commutative-semiring arithmetic
-- layer above the minimal finite-factorisation algebra.

record MarxPowerArithmeticLaws
  (A : MarxAlgebra)
  : Set₁ where
  field
    powerLaws : MarxPowerAlgebraLaws A
    addCommLaw : ∀ x y → _+_ A x y ≡ _+_ A y x
    mulInterchangeLaw :
      ∀ a b x y →
      _*_ A (_*_ A a b) (_*_ A x y)
      ≡ _*_ A (_*_ A a x) (_*_ A b y)

open MarxPowerArithmeticLaws public

_+N_ : Nat → Nat → Nat
m +N zero = m
m +N suc n = suc (m +N n)

natCastAdd :
  {A : MarxAlgebra} →
  (L : MarxPowerArithmeticLaws A) →
  ∀ m n →
  natCast {A} (m +N n)
  ≡ _+_ A (natCast m) (natCast n)
natCastAdd {A} L m zero =
  sym (addZeroRightLaw (powerLaws L) (natCast m))
natCastAdd {A} L m (suc n) =
  trans
    (cong (λ t → _+_ A t (one A)) (natCastAdd L m n))
    (addAssocLaw (powerLaws L) (natCast m) (natCast n) (one A))

natScaleAdd :
  {A : MarxAlgebra} →
  (L : MarxPowerArithmeticLaws A) →
  ∀ m n x →
  natScale (m +N n) x
  ≡ _+_ A (natScale m x) (natScale n x)
natScaleAdd {A} L m n x =
  trans
    (cong (λ coefficient → _*_ A coefficient x) (natCastAdd L m n))
    (distribRightLaw (powerLaws L) (natCast m) (natCast n) x)

powerZero :
  {A : MarxAlgebra} →
  ∀ x → powerFunction {A} zero x ≡ one A
powerZero x = refl

powerSuccessor :
  {A : MarxAlgebra} →
  ∀ n x →
  powerFunction {A} (suc n) x
  ≡ _*_ A (powerFunction n x) x
powerSuccessor n x = refl

powerOne :
  {A : MarxAlgebra} →
  ∀ n → powerFunction {A} n (one A) ≡ one A
powerOne {A} zero = refl
powerOne {A} (suc n) =
  trans
    (cong (λ t → _*_ A t (one A)) (powerOne n))
    (mulOneRight A (one A))

powerAdd :
  {A : MarxAlgebra} →
  ∀ m n x →
  powerFunction {A} (m +N n) x
  ≡ _*_ A (powerFunction m x) (powerFunction n x)
powerAdd {A} m zero x = sym (mulOneRight A (powerFunction m x))
powerAdd {A} m (suc n) x =
  trans
    (cong (λ t → _*_ A t x) (powerAdd m n x))
    (mulAssoc A (powerFunction m x) (powerFunction n x) x)

powerMulBase :
  {A : MarxAlgebra} →
  (L : MarxPowerArithmeticLaws A) →
  ∀ n x y →
  powerFunction n (_*_ A x y)
  ≡ _*_ A (powerFunction n x) (powerFunction n y)
powerMulBase {A} L zero x y =
  sym (mulOneRight A (one A))
powerMulBase {A} L (suc n) x y =
  trans
    (cong
      (λ t → _*_ A t (_*_ A x y))
      (powerMulBase L n x y))
    (mulInterchangeLaw L
      (powerFunction n x)
      (powerFunction n y)
      x y)

------------------------------------------------------------------------
-- Zero-safe displayed power rule.

powerDerivativeValue :
  {A : MarxAlgebra} →
  Nat → Carrier A → Carrier A
powerDerivativeValue {A} zero x = zero A
powerDerivativeValue {A} (suc n) x =
  natScale (suc n) (powerFunction n x)

powerDerivative :
  {A : MarxAlgebra} →
  (L : MarxPowerAlgebraLaws A) →
  ∀ n x →
  marxDerivative (powerFactorisation n) x
  ≡ powerDerivativeValue n x
powerDerivative L zero x = powerDerivativeZero x
powerDerivative L (suc n) x = powerDerivativeNatScale L n x
