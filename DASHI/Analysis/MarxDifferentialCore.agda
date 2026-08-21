module DASHI.Analysis.MarxDifferentialCore where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong)
open import Agda.Primitive using (Set)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Marx differential algebra.
--
-- The governing sequence is:
--
--   original function
--     -> finite transport
--     -> preliminary derived function
--     -> factorisation receipt
--     -> evaluation at boundary (diagonal)
--
-- Derivatives exist as concrete mathematical objects (preliminary functions)
-- rather than limit assertions.

record MarxAlgebra : Set₁ where
  infixl 20 _+_ _-_
  infixl 30 _*_
  field
    Carrier : Set
    zero one : Carrier
    _+_ _-_ _*_ : Carrier → Carrier → Carrier
    _≢_ : Carrier → Carrier → Set

    subSelf : ∀ (c : Carrier) → c - c ≡ zero
    mulZeroRight : ∀ (c : Carrier) → c * zero ≡ zero
    mulOneRight : ∀ (c : Carrier) → c * one ≡ c
    mulCommutative : ∀ (a b : Carrier) → a * b ≡ b * a
    mulAssoc : ∀ (a b c : Carrier) → (a * b) * c ≡ a * (b * c)

    addDifferenceFactor :
      ∀ {x x₁ a a₁ b b₁ A B} →
      a₁ - a ≡ (x₁ - x) * A →
      b₁ - b ≡ (x₁ - x) * B →
      (a₁ + b₁) - (a + b) ≡ (x₁ - x) * (A + B)

    productDifferenceFactor :
      ∀ {x x₁ a a₁ b b₁ A B} →
      a₁ - a ≡ (x₁ - x) * A →
      b₁ - b ≡ (x₁ - x) * B →
      (a₁ * b₁) - (a * b)
      ≡ (x₁ - x) * ((A * b₁) + (a * B))

open MarxAlgebra public

Function : MarxAlgebra → Set
Function A = Carrier A → Carrier A

------------------------------------------------------------------------
-- Finite variation.

inputDifference :
  (A : MarxAlgebra) →
  Carrier A → Carrier A → Carrier A
inputDifference A x x₁ = MarxAlgebra._-_ A x₁ x

functionDifference :
  (A : MarxAlgebra) →
  Function A → Carrier A → Carrier A → Carrier A
functionDifference A f x x₁ = MarxAlgebra._-_ A (f x₁) (f x)

record FiniteTransport
  (A : MarxAlgebra)
  (f : Function A)
  (x x₁ : Carrier A)
  : Set where
  field
    inputDistinct : MarxAlgebra._≢_ A x₁ x

------------------------------------------------------------------------
-- Preliminary and final derived functions.

record MarxFactorisation
  (A : MarxAlgebra)
  (f : Function A)
  : Set where
  field
    preliminary : Carrier A → Carrier A → Carrier A

    finiteFactorisation :
      ∀ x x₁ →
      functionDifference A f x x₁
      ≡ MarxAlgebra._*_ A
          (inputDifference A x x₁)
          (preliminary x x₁)

open MarxFactorisation public

marxDerivative :
  {A : MarxAlgebra} →
  {f : Function A} →
  MarxFactorisation A f →
  Function A
marxDerivative F x = preliminary F x x

record MarxDifferentiable
  (A : MarxAlgebra)
  (f : Function A)
  : Set₁ where
  field
    factorisation : MarxFactorisation A f

open MarxDifferentiable public

------------------------------------------------------------------------
-- Premature diagonal quotient is impossible.
--
-- Standard limits try to evaluate f(x₁) - f(x) / x₁ - x at x₁ = x,
-- which produces 0/0.  Marx factorisation extracts the preliminary function
-- FIRST, where evaluation at x₁ = x is completely well-defined.

diagonalEvaluationBlocked :
  (A : MarxAlgebra) →
  (x : Carrier A) →
  inputDifference A x x ≡ zero A
diagonalEvaluationBlocked A x = subSelf A x

------------------------------------------------------------------------
-- Exact elementary derivatives.

constantFunction :
  {A : MarxAlgebra} →
  Carrier A → Function A
constantFunction c _ = c

identityFunction :
  {A : MarxAlgebra} →
  Function A
identityFunction x = x

constantFactorisation :
  {A : MarxAlgebra} →
  (c : Carrier A) →
  MarxFactorisation A (constantFunction {A} c)
constantFactorisation {A} c =
  record
    { preliminary = λ _ _ → zero A
    ; finiteFactorisation = λ x x₁ →
        trans
          (subSelf A c)
          (sym (mulZeroRight A (inputDifference A x x₁)))
    }

identityFactorisation :
  {A : MarxAlgebra} →
  MarxFactorisation A (identityFunction {A})
identityFactorisation {A} =
  record
    { preliminary = λ _ _ → one A
    ; finiteFactorisation = λ x x₁ →
        sym (mulOneRight A (inputDifference A x x₁))
    }

constantDerivative :
  {A : MarxAlgebra} (c x : Carrier A) →
  marxDerivative (constantFactorisation {A} c) x ≡ zero A
constantDerivative {A} c x = refl

identityDerivative :
  {A : MarxAlgebra} (x : Carrier A) →
  marxDerivative (identityFactorisation {A}) x ≡ one A
identityDerivative {A} x = refl

addFunctions :
  {A : MarxAlgebra} →
  Function A → Function A → Function A
addFunctions {A} f g x = MarxAlgebra._+_ A (f x) (g x)

multiplyFunctions :
  {A : MarxAlgebra} →
  Function A → Function A → Function A
multiplyFunctions {A} f g x = MarxAlgebra._*_ A (f x) (g x)

addFactorisations :
  {A : MarxAlgebra} →
  {f g : Function A} →
  MarxFactorisation A f →
  MarxFactorisation A g →
  MarxFactorisation A (addFunctions {A} f g)
addFactorisations {A} {f} {g} F G =
  record
    { preliminary = λ x x₁ →
        MarxAlgebra._+_ A (preliminary F x x₁) (preliminary G x x₁)
    ; finiteFactorisation = λ x x₁ →
        addDifferenceFactor A
          (finiteFactorisation F x x₁)
          (finiteFactorisation G x x₁)
    }

productFactorisations :
  {A : MarxAlgebra} →
  {f g : Function A} →
  MarxFactorisation A f →
  MarxFactorisation A g →
  MarxFactorisation A (multiplyFunctions {A} f g)
productFactorisations {A} {f} {g} F G =
  record
    { preliminary = λ x x₁ →
        MarxAlgebra._+_ A
          (MarxAlgebra._*_ A (preliminary F x x₁) (g x₁))
          (MarxAlgebra._*_ A (f x) (preliminary G x x₁))
    ; finiteFactorisation = λ x x₁ →
        productDifferenceFactor A
          (finiteFactorisation F x x₁)
          (finiteFactorisation G x x₁)
    }

sumRule :
  {A : MarxAlgebra} →
  {f g : Function A} →
  (F : MarxFactorisation A f) →
  (G : MarxFactorisation A g) →
  (x : Carrier A) →
  marxDerivative (addFactorisations {A} F G) x
  ≡ MarxAlgebra._+_ A (marxDerivative F x) (marxDerivative G x)
sumRule {A} F G x = refl

productRule :
  {A : MarxAlgebra} →
  {f g : Function A} →
  (F : MarxFactorisation A f) →
  (G : MarxFactorisation A g) →
  (x : Carrier A) →
  marxDerivative (productFactorisations {A} F G) x
  ≡ MarxAlgebra._+_ A
      (MarxAlgebra._*_ A (marxDerivative F x) (g x))
      (MarxAlgebra._*_ A (f x) (marxDerivative G x))
productRule {A} F G x = refl

------------------------------------------------------------------------
-- Chain rule from nested finite transports.

compose :
  {A : MarxAlgebra} →
  Function A → Function A → Function A
compose f g x = f (g x)

chainFactorisation :
  {A : MarxAlgebra} →
  {f g : Function A} →
  MarxFactorisation A f →
  MarxFactorisation A g →
  MarxFactorisation A (compose {A} f g)
chainFactorisation {A} {f} {g} F G =
  record
    { preliminary = λ x x₁ →
        MarxAlgebra._*_ A
          (preliminary G x x₁)
          (preliminary F (g x) (g x₁))
    ; finiteFactorisation = λ x x₁ →
        trans
          (finiteFactorisation F (g x) (g x₁))
          (trans
            (cong
              (λ d → MarxAlgebra._*_ A d (preliminary F (g x) (g x₁)))
              (finiteFactorisation G x x₁))
            (mulAssoc A
              (inputDifference A x x₁)
              (preliminary G x x₁)
              (preliminary F (g x) (g x₁))))
    }

chainRule :
  {A : MarxAlgebra} →
  {f g : Function A} →
  (F : MarxFactorisation A f) →
  (G : MarxFactorisation A g) →
  (x : Carrier A) →
  marxDerivative (chainFactorisation {A} F G) x
  ≡ MarxAlgebra._*_ A
      (marxDerivative G x)
      (marxDerivative F (g x))
chainRule {A} F G x = refl

------------------------------------------------------------------------
-- Quotient rule as product with an explicitly receipted reciprocal.

record ReciprocalStructure
  (A : MarxAlgebra)
  : Set₁ where
  field
    Nonzero : Carrier A → Set
    reciprocal : (x : Carrier A) → Nonzero x → Carrier A

open ReciprocalStructure public

record ReciprocalFactorisation
  {A : MarxAlgebra}
  (Q : ReciprocalStructure A)
  (g : Function A)
  (nonzero : ∀ x → Nonzero Q (g x))
  : Set₁ where
  field
    receipt :
      MarxFactorisation A
        (λ x → reciprocal Q (g x) (nonzero x))

open ReciprocalFactorisation public

quotientFunction :
  {A : MarxAlgebra} →
  (Q : ReciprocalStructure A) →
  (f g : Function A) →
  (nonzero : ∀ x → Nonzero Q (g x)) →
  Function A
quotientFunction {A} Q f g nonzero x =
  MarxAlgebra._*_ A (f x) (reciprocal Q (g x) (nonzero x))

quotientFactorisation :
  {A : MarxAlgebra} →
  (Q : ReciprocalStructure A) →
  {f g : Function A} →
  (nonzero : ∀ x → Nonzero Q (g x)) →
  MarxFactorisation A f →
  ReciprocalFactorisation Q g nonzero →
  MarxFactorisation A (quotientFunction {A} Q f g nonzero)
quotientFactorisation {A} Q {f} {g} nonzero F G⁻¹ =
  productFactorisations {A} F (receipt G⁻¹)

record QuotientRuleNormalisation
  {A : MarxAlgebra}
  (Q : ReciprocalStructure A)
  : Set₁ where
  field
    quotientRuleFormula :
      (f g : Function A) →
      (nonzero : ∀ x → Nonzero Q (g x)) →
      (F : MarxFactorisation A f) →
      (G⁻¹ : ReciprocalFactorisation Q g nonzero) →
      (x : Carrier A) →
      marxDerivative (quotientFactorisation {A} Q nonzero F G⁻¹) x
      ≡ MarxAlgebra._+_ A
          (MarxAlgebra._*_ A (marxDerivative F x) (reciprocal Q (g x) (nonzero x)))
          (MarxAlgebra._*_ A (f x) (marxDerivative (receipt G⁻¹) x))

open QuotientRuleNormalisation public

canonicalQuotientRuleNormalisation :
  {A : MarxAlgebra} →
  (Q : ReciprocalStructure A) →
  QuotientRuleNormalisation Q
canonicalQuotientRuleNormalisation {A} Q =
  record
    { quotientRuleFormula = λ f g nonzero F G⁻¹ x → refl
    }
