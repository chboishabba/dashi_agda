module DASHI.Foundations.ElementaryCalculatorDomains where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)

open import DASHI.Foundations.ElementaryCalculator

------------------------------------------------------------------------
-- There is no single useful principal-branch domain closed under every
-- calculator primitive.  This package assigns each source tree its exact
-- semantic and compiled-domain obligations and produces the correctness proof.

record CalculatorDomainModel : Set₁ where
  field
    Value : Set
    Environment : Set
    evaluateSource : Environment → CalculatorExpr → Value
    evaluateCompiled : Environment → CalculatorExpr → Value
    DefinedSource : Environment → CalculatorExpr → Set
    DefinedCompiled : Environment → CalculatorExpr → Set

open CalculatorDomainModel public

record ConstructorSpecificCalculatorDomains
  (M : CalculatorDomainModel) : Set₁ where
  field
    NonZero : Value M → Set
    Positive : Value M → Set
    PrincipalLogDomain : Value M → Set
    PrincipalSqrtDomain : Value M → Set

    variableDefined : ∀ ρ x → DefinedSource M ρ (variable x)
    integerDefined : ∀ ρ n → DefinedSource M ρ (integer n)
    rationalDefined : ∀ ρ q → DefinedSource M ρ (rational q)

    divideDomain : ∀ ρ x y →
      DefinedSource M ρ x →
      DefinedSource M ρ y →
      NonZero (evaluateSource M ρ y) →
      DefinedSource M ρ (calcDivide x y)

    logDomain : ∀ ρ x →
      DefinedSource M ρ x →
      PrincipalLogDomain (evaluateSource M ρ x) →
      DefinedSource M ρ (calcLog x)

    powerDomain : ∀ ρ x y →
      DefinedSource M ρ x →
      DefinedSource M ρ y →
      PrincipalLogDomain (evaluateSource M ρ x) →
      DefinedSource M ρ (calcPower x y)

    sqrtDomain : ∀ ρ x →
      DefinedSource M ρ x →
      PrincipalSqrtDomain (evaluateSource M ρ x) →
      DefinedSource M ρ (calcSqrt x)

    tanDomain : ∀ ρ x →
      DefinedSource M ρ x →
      NonZero (evaluateSource M ρ (calcCos x)) →
      DefinedSource M ρ (calcTan x)

    tanhDomain : ∀ ρ x →
      DefinedSource M ρ x →
      NonZero (evaluateSource M ρ (calcCosh x)) →
      DefinedSource M ρ (calcTanh x)

open ConstructorSpecificCalculatorDomains public

record CalculatorCompilationClosure
  (M : CalculatorDomainModel)
  (D : ConstructorSpecificCalculatorDomains M) : Set₁ where
  field
    compilationDefined : ∀ ρ t →
      DefinedSource M ρ t →
      DefinedCompiled M ρ t

    compilationCorrect : ∀ ρ t →
      DefinedSource M ρ t →
      evaluateCompiled M ρ t ≡ evaluateSource M ρ t

  certifiedCompilation : ∀ ρ t →
    DefinedSource M ρ t →
    Σ (DefinedCompiled M ρ t)
      (λ _ → evaluateCompiled M ρ t ≡ evaluateSource M ρ t)
  certifiedCompilation ρ t defined =
    compilationDefined ρ t defined , compilationCorrect ρ t defined

open CalculatorCompilationClosure public

record PositiveArithmeticClosure
  (M : CalculatorDomainModel)
  (D : ConstructorSpecificCalculatorDomains M) : Set₁ where
  field
    addPositive : ∀ ρ x y →
      DefinedSource M ρ x → DefinedSource M ρ y →
      Positive D (evaluateSource M ρ x) →
      Positive D (evaluateSource M ρ y) →
      Positive D (evaluateSource M ρ (calcAdd x y))

    multiplyPositive : ∀ ρ x y →
      DefinedSource M ρ x → DefinedSource M ρ y →
      Positive D (evaluateSource M ρ x) →
      Positive D (evaluateSource M ρ y) →
      DefinedSource M ρ (calcMultiply x y)

    dividePositive : ∀ ρ x y →
      DefinedSource M ρ x → DefinedSource M ρ y →
      Positive D (evaluateSource M ρ x) →
      Positive D (evaluateSource M ρ y) →
      DefinedSource M ρ (calcDivide x y)

open PositiveArithmeticClosure public
