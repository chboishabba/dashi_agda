module DASHI.Analysis.MarxPowerArithmetic where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Set₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

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

open MarxPowerArithmeticLaws public

_+N_ : Nat → Nat → Nat
zero +N n = n
suc m +N n = suc (m +N n)

natCastAdd :
  {A : MarxAlgebra} →
  (L : MarxPowerArithmeticLaws A) →
  ∀ m n →
  natCast {A} (m +N n)
  ≡ _+_ A (natCast m) (natCast n)
natCastAdd {A} L zero n =
  sym (addZeroLeftLaw (powerLaws L) (natCast n))
natCastAdd {A} L (suc m) n =
  trans
    (cong (λ t → _+_ A t (one A)) (natCastAdd L m n))
    (trans
      (addAssocLaw (powerLaws L) (natCast m) (natCast n) (one A))
      (trans
        (cong
          (λ t → _+_ A (natCast m) t)
          (addCommLaw L (natCast n) (one A)))
        (sym
          (addAssocLaw (powerLaws L)
            (natCast m) (one A) (natCast n)))))

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
    (trans
      (sym
        (mulAssoc A
          (_*_ A (powerFunction n x) (powerFunction n y))
          x y))
      (trans
        (cong
          (λ t → _*_ A t y)
          (trans
            (mulAssoc A (powerFunction n x) (powerFunction n y) x)
            (trans
              (cong
                (λ t → _*_ A (powerFunction n x) t)
                (mulCommLaw (powerLaws L) (powerFunction n y) x))
              (sym
                (mulAssoc A
                  (powerFunction n x) x
                  (powerFunction n y))))))
        (mulAssoc A
          (_*_ A (powerFunction n x) x)
          (powerFunction n y)
          y)))

------------------------------------------------------------------------
-- Zero-safe displayed power rule.

data PowerDerivativeNormalForm
  (A : MarxAlgebra)
  : Nat → Set where
  zeroPowerDerivative :
    PowerDerivativeNormalForm A zero
  successorPowerDerivative :
    ∀ n →
    PowerDerivativeNormalForm A (suc n)

powerDerivativeZeroSafe :
  {A : MarxAlgebra} →
  (L : MarxPowerAlgebraLaws A) →
  ∀ n x →
  PowerDerivativeNormalForm A n
powerDerivativeZeroSafe L zero x = zeroPowerDerivative
powerDerivativeZeroSafe L (suc n) x = successorPowerDerivative n
