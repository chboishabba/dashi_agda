module DASHI.Analysis.MarxDifferentialCore where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set; Set₁)
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
--     -> lawful diagonal collapse
--     -> final derived function.
--
-- No quotient at x₁ = x is formed.  The diagonal is entered only after the
-- finite difference has been factorised by x₁ - x.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Algebra required by the exact finite-transport proofs.

record MarxAlgebra : Set₁ where
  infixl 20 _+_ _-_
  infixl 30 _*_
  field
    Carrier : Set
    zero one : Carrier
    _+_ _-_ _*_ : Carrier → Carrier → Carrier

    subSelf : ∀ x → x - x ≡ zero
    mulZeroRight : ∀ x → x * zero ≡ zero
    mulOneRight : ∀ x → x * one ≡ x
    mulAssoc : ∀ x y z → (x * y) * z ≡ x * (y * z)

    -- Normalisation laws used by closure constructors.  Keeping these laws
    -- explicit prevents a hidden ring solver or an untracked rewrite policy.
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
inputDifference A x x₁ = _-_ A x₁ x

functionDifference :
  (A : MarxAlgebra) →
  Function A → Carrier A → Carrier A → Carrier A
functionDifference A f x x₁ = _-_ A (f x₁) (f x)

record FiniteTransport
  (A : MarxAlgebra)
  (f : Function A)
  (x x₁ : Carrier A)
  : Set where
  field
    inputDistinct : x₁ ≢ x

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
      ≡ _*_ A
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

record RawDiagonalQuotient
  (A : MarxAlgebra)
  (f : Function A)
  (x : Carrier A)
  : Set where
  field
    denominatorNonzero : inputDifference A x x ≢ zero A

rawDiagonalQuotientImpossible :
  {A : MarxAlgebra} →
  {f : Function A} →
  {x : Carrier A} →
  RawDiagonalQuotient A f x →
  ⊥
rawDiagonalQuotientImpossible {A} {x = x} raw =
  RawDiagonalQuotient.denominatorNonzero raw
    (subSelf A x)

-- A diagonal value is lawful only because the preliminary function already
-- exists independently of division by the zero input difference.
record LawfulDiagonalCollapse
  (A : MarxAlgebra)
  (f : Function A)
  : Set₁ where
  field
    factorisationReceipt : MarxFactorisation A f
    finalDerived : Function A
    finalIsDiagonal :
      ∀ x →
      finalDerived x
      ≡ preliminary factorisationReceipt x x

canonicalDiagonalCollapse :
  {A : MarxAlgebra} →
  {f : Function A} →
  (F : MarxFactorisation A f) →
  LawfulDiagonalCollapse A f
canonicalDiagonalCollapse F =
  record
    { factorisationReceipt = F
    ; finalDerived = marxDerivative F
    ; finalIsDiagonal = λ x → refl
    }

------------------------------------------------------------------------
-- Exact algebraic closure.

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
  MarxFactorisation A (constantFunction c)
constantFactorisation {A} c =
  record
    { preliminary = λ _ _ → zero A
    ; finiteFactorisation = λ x x₁ →
        trans
          (subSelf A c)
          (sym (mulZeroRight A (inputDifference A x x₁)))
    }
  where
    sym : {X : Set} {u v : X} → u ≡ v → v ≡ u
    sym refl = refl

identityFactorisation :
  {A : MarxAlgebra} →
  MarxFactorisation A identityFunction
identityFactorisation {A} =
  record
    { preliminary = λ _ _ → one A
    ; finiteFactorisation = λ x x₁ →
        sym (mulOneRight A (inputDifference A x x₁))
    }
  where
    sym : {X : Set} {u v : X} → u ≡ v → v ≡ u
    sym refl = refl

constantDerivative :
  {A : MarxAlgebra} →
  (c x : Carrier A) →
  marxDerivative (constantFactorisation c) x ≡ zero A
constantDerivative c x = refl

identityDerivative :
  {A : MarxAlgebra} →
  (x : Carrier A) →
  marxDerivative identityFactorisation x ≡ one A
identityDerivative x = refl

addFunctions :
  {A : MarxAlgebra} →
  Function A → Function A → Function A
addFunctions {A} f g x = _+_ A (f x) (g x)

multiplyFunctions :
  {A : MarxAlgebra} →
  Function A → Function A → Function A
multiplyFunctions {A} f g x = _*_ A (f x) (g x)

addFactorisations :
  {A : MarxAlgebra} →
  {f g : Function A} →
  MarxFactorisation A f →
  MarxFactorisation A g →
  MarxFactorisation A (addFunctions f g)
addFactorisations {A} {f} {g} F G =
  record
    { preliminary = λ x x₁ →
        _+_ A (preliminary F x x₁) (preliminary G x x₁)
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
  MarxFactorisation A (multiplyFunctions f g)
productFactorisations {A} {f} {g} F G =
  record
    { preliminary = λ x x₁ →
        _+_ A
          (_*_ A (preliminary F x x₁) (g x₁))
          (_*_ A (f x) (preliminary G x x₁))
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
  marxDerivative (addFactorisations F G) x
  ≡ _+_ A (marxDerivative F x) (marxDerivative G x)
sumRule F G x = refl

productRule :
  {A : MarxAlgebra} →
  {f g : Function A} →
  (F : MarxFactorisation A f) →
  (G : MarxFactorisation A g) →
  (x : Carrier A) →
  marxDerivative (productFactorisations F G) x
  ≡ _+_ A
      (_*_ A (marxDerivative F x) (g x))
      (_*_ A (f x) (marxDerivative G x))
productRule F G x = refl

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
  MarxFactorisation A (compose f g)
chainFactorisation {A} {f} {g} F G =
  record
    { preliminary = λ x x₁ →
        _*_ A
          (preliminary G x x₁)
          (preliminary F (g x) (g x₁))
    ; finiteFactorisation = λ x x₁ →
        trans
          (finiteFactorisation F (g x) (g x₁))
          (trans
            (cong
              (λ d → _*_ A d (preliminary F (g x) (g x₁)))
              (finiteFactorisation G x x₁))
            (mulAssoc A
              (inputDifference A x x₁)
              (preliminary G x x₁)
              (preliminary F (g x) (g x₁))))
    }
  where
    cong :
      {X Y : Set} {u v : X} →
      (h : X → Y) → u ≡ v → h u ≡ h v
    cong h refl = refl

chainRule :
  {A : MarxAlgebra} →
  {f g : Function A} →
  (F : MarxFactorisation A f) →
  (G : MarxFactorisation A g) →
  (x : Carrier A) →
  marxDerivative (chainFactorisation F G) x
  ≡ _*_ A
      (marxDerivative G x)
      (marxDerivative F (g x))
chainRule F G x = refl

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
  _*_ A (f x) (reciprocal Q (g x) (nonzero x))

quotientFactorisation :
  {A : MarxAlgebra} →
  (Q : ReciprocalStructure A) →
  {f g : Function A} →
  (nonzero : ∀ x → Nonzero Q (g x)) →
  MarxFactorisation A f →
  ReciprocalFactorisation Q g nonzero →
  MarxFactorisation A (quotientFunction Q f g nonzero)
quotientFactorisation Q nonzero F G⁻¹ =
  productFactorisations F (receipt G⁻¹)

record QuotientRuleNormalisation
  {A : MarxAlgebra}
  (Q : ReciprocalStructure A)
  : Set₁ where
  field
    quotientRuleFormula :
      {f g : Function A} →
      (nonzero : ∀ x → Nonzero Q (g x)) →
      (F : MarxFactorisation A f) →
      (G : MarxFactorisation A g) →
      (G⁻¹ : ReciprocalFactorisation Q g nonzero) →
      (x : Carrier A) →
      Carrier A

    quotientRuleMatchesCollapsedProduct :
      {f g : Function A} →
      (nonzero : ∀ x → Nonzero Q (g x)) →
      (F : MarxFactorisation A f) →
      (G : MarxFactorisation A g) →
      (G⁻¹ : ReciprocalFactorisation Q g nonzero) →
      (x : Carrier A) →
      marxDerivative
        (quotientFactorisation Q nonzero F G⁻¹)
        x
      ≡ quotientRuleFormula nonzero F G G⁻¹ x

-- The explicit denominator-squared presentation is deliberately kept behind
-- QuotientRuleNormalisation: it requires a selected subtraction, reciprocal,
-- commutativity, and denominator-normalisation policy.  No such policy is
-- inferred merely from the existence of a reciprocal function.
