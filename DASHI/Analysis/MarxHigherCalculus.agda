module DASHI.Analysis.MarxHigherCalculus where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Set; Set₁)

open import DASHI.Analysis.MarxDifferentialCore public

------------------------------------------------------------------------
-- Iterated derivatives.

iterateDerivative :
  {A : MarxAlgebra} →
  (D : Function A → Function A) →
  Nat → Function A → Function A
iterateDerivative D zero f = f
iterateDerivative D (suc n) f = D (iterateDerivative D n f)

iterateDerivativeZero :
  {A : MarxAlgebra} →
  (D : Function A → Function A) →
  (f : Function A) →
  iterateDerivative D zero f ≡ f
iterateDerivativeZero D f = refl

iterateDerivativeSuccessor :
  {A : MarxAlgebra} →
  (D : Function A → Function A) →
  (n : Nat) →
  (f : Function A) →
  iterateDerivative D (suc n) f
  ≡ D (iterateDerivative D n f)
iterateDerivativeSuccessor D n f = refl

------------------------------------------------------------------------
-- A closed Marx-differentiable family supplies a factorisation for every
-- function reached by the derivative operator.

record ClosedMarxDifferentialFamily
  (A : MarxAlgebra)
  : Set₁ where
  field
    admissible : Function A → Set
    factorise :
      (f : Function A) →
      admissible f →
      MarxFactorisation A f

    derivativeClosed :
      (f : Function A) →
      (pf : admissible f) →
      admissible (marxDerivative (factorise f pf))

open ClosedMarxDifferentialFamily public

familyDerivative :
  {A : MarxAlgebra} →
  (C : ClosedMarxDifferentialFamily A) →
  (f : Function A) →
  admissible C f →
  Function A
familyDerivative C f pf =
  marxDerivative (factorise C f pf)

record HigherDerivativeTower
  {A : MarxAlgebra}
  (C : ClosedMarxDifferentialFamily A)
  (f : Function A)
  : Set₁ where
  field
    baseAdmissible : admissible C f
    derivativeAtOrder : Nat → Function A
    admissibleAtOrder :
      (n : Nat) →
      admissible C (derivativeAtOrder n)
    orderZero : derivativeAtOrder zero ≡ f
    orderSuccessor :
      ∀ n →
      derivativeAtOrder (suc n)
      ≡ familyDerivative C
          (derivativeAtOrder n)
          (admissibleAtOrder n)

------------------------------------------------------------------------
-- Taylor coefficients.

record TaylorCoefficientStructure
  (A : MarxAlgebra)
  : Set₁ where
  field
    factorial : Nat → Carrier A
    divide : Carrier A → Carrier A → Carrier A
    denominatorAdmissible : Nat → Set

open TaylorCoefficientStructure public

record TaylorExpansionData
  {A : MarxAlgebra}
  (T : TaylorCoefficientStructure A)
  (derivativeAtOrder : Nat → Function A)
  (centre : Carrier A)
  : Set₁ where
  field
    coefficient : Nat → Carrier A
    coefficientLaw :
      ∀ n →
      coefficient n
      ≡ divide T
          (derivativeAtOrder n centre)
          (factorial T n)

------------------------------------------------------------------------
-- Directional and Frechet differentiation.

record LinearMap
  (Scalar V W : Set)
  : Set₁ where
  field
    apply : V → W

open LinearMap public

record DirectionalDerivative
  (Scalar V W : Set)
  (f : V → W)
  : Set₁ where
  field
    at : V → V → W

record FrechetDerivative
  (Scalar V W : Set)
  (f : V → W)
  : Set₁ where
  field
    derivative : V → LinearMap Scalar V W
    remainderControl : Set

open FrechetDerivative public

record DirectionalFrechetCompatibility
  {Scalar V W : Set}
  {f : V → W}
  (directional : DirectionalDerivative Scalar V W f)
  (frechet : FrechetDerivative Scalar V W f)
  : Set₁ where
  field
    directionalIsFrechetApplication :
      ∀ x v →
      DirectionalDerivative.at directional x v
      ≡ apply (derivative frechet x) v

------------------------------------------------------------------------
-- Jacobians, forms, and integration.

record CoordinateSystem
  (Scalar V : Set)
  : Set₁ where
  field
    Index : Set
    basis : Index → V

record Jacobian
  (Scalar V W : Set)
  (f : V → W)
  : Set₁ where
  field
    Row : Set
    Column : Set
    entry : V → Row → Column → Scalar

record DifferentialForm
  (Scalar V : Set)
  : Set₁ where
  field
    degree : Nat
    evaluate : V → Scalar

record ExteriorDerivative
  (Scalar V : Set)
  : Set₁ where
  field
    zeroForm : DifferentialForm Scalar V
    d : DifferentialForm Scalar V → DifferentialForm Scalar V
    dSquaredZero :
      ∀ omega →
      d (d omega) ≡ zeroForm

record IntegrationInterface
  (Scalar Domain : Set)
  : Set₁ where
  field
    integrate : (Domain → Scalar) → Scalar
    integrable : (Domain → Scalar) → Set

record FundamentalTheoremBridge
  {A : MarxAlgebra}
  (I : IntegrationInterface (Carrier A) (Carrier A))
  : Set₁ where
  field
    antiderivative : Function A → Function A
    differentiableIntegrands : Function A → Set
    derivativeOfIntegral :
      (f : Function A) →
      differentiableIntegrands f →
      Set
    integralOfDerivative :
      (f : Function A) →
      differentiableIntegrands f →
      Set

------------------------------------------------------------------------
-- Higher-calculus completion bundle.

record MarxHigherCalculusBundle : Set₁ where
  field
    algebra : MarxAlgebra
    closedFamily : ClosedMarxDifferentialFamily algebra
    taylor : TaylorCoefficientStructure algebra
    Vector : Set
    directionalFamily :
      (f : Vector → Vector) →
      DirectionalDerivative (Carrier algebra) Vector Vector f
    frechetFamily :
      (f : Vector → Vector) →
      FrechetDerivative (Carrier algebra) Vector Vector f
    integration :
      IntegrationInterface (Carrier algebra) (Carrier algebra)
