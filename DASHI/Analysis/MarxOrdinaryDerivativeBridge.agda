module DASHI.Analysis.MarxOrdinaryDerivativeBridge where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (Set; Set₁)

open import DASHI.Analysis.MarxDifferentialCore public

------------------------------------------------------------------------
-- Remainder-based ordinary derivative surface.
--
-- The current ConstructiveRealSpine supplies a completed ordered carrier,
-- sequences, Cauchy convergence, and transcendental packages, but it does not
-- yet expose a normed-vector derivative.  This module therefore states the
-- exact additional structure instead of silently identifying equality of
-- finite factorisations with analytic differentiability.

record RemainderDerivativeStructure
  (A : MarxAlgebra)
  : Set₁ where
  field
    SmallParameter : Set
    parameterValue : SmallParameter → Carrier A
    tendsToZero : (SmallParameter → Carrier A) → Set

open RemainderDerivativeStructure public

record OrdinaryDerivativeAt
  {A : MarxAlgebra}
  (R : RemainderDerivativeStructure A)
  (f : Function A)
  (x : Carrier A)
  : Set₁ where
  field
    linearCoefficient : Carrier A
    remainder : SmallParameter R → Carrier A

    expansion :
      ∀ h →
      f (_+_ A x (parameterValue R h))
      ≡ _+_ A
          (f x)
          (_+_ A
            (_*_ A linearCoefficient (parameterValue R h))
            (remainder h))

    normalizedRemainderVanishes :
      tendsToZero R remainder

open OrdinaryDerivativeAt public

record ContinuousDiagonal
  {A : MarxAlgebra}
  {f : Function A}
  (F : MarxFactorisation A f)
  (x : Carrier A)
  : Set₁ where
  field
    diagonalApproach : Set

-- The compatibility theorem needs a genuine analytic argument connecting the
-- two-variable preliminary function to the remainder quotient.  That argument
-- is isolated as an authority because the existing ordinary-real spine has no
-- topology/norm interface from which it can yet be derived.
record MarxOrdinaryCompatibilityAuthority
  {A : MarxAlgebra}
  (R : RemainderDerivativeStructure A)
  : Set₁ where
  field
    factorisationContinuousDiagonalImpliesOrdinary :
      {f : Function A} →
      (F : MarxFactorisation A f) →
      (x : Carrier A) →
      ContinuousDiagonal F x →
      OrdinaryDerivativeAt R f x →
      marxDerivative F x
      ≡ linearCoefficient

open MarxOrdinaryCompatibilityAuthority public

marxDerivativeAgreesWithOrdinaryDerivative :
  {A : MarxAlgebra} →
  {R : RemainderDerivativeStructure A} →
  (authority : MarxOrdinaryCompatibilityAuthority R) →
  {f : Function A} →
  (F : MarxFactorisation A f) →
  (x : Carrier A) →
  ContinuousDiagonal F x →
  (ordinary : OrdinaryDerivativeAt R f x) →
  marxDerivative F x
  ≡ linearCoefficient ordinary
marxDerivativeAgreesWithOrdinaryDerivative authority F x continuous ordinary =
  factorisationContinuousDiagonalImpliesOrdinary
    authority F x continuous ordinary

------------------------------------------------------------------------
-- Completion seam for the repository's constructive-real implementation.

record ConstructiveRealDerivativeSeam : Set₁ where
  field
    algebra : MarxAlgebra
    remainderStructure : RemainderDerivativeStructure algebra
    compatibility : MarxOrdinaryCompatibilityAuthority remainderStructure

-- An inhabitant of ConstructiveRealDerivativeSeam is the exact object needed
-- to place Marx differentiation inside the completed ordinary-real calculus.
-- It must be built from a selected constructive real, its norm/topology, and a
-- proved diagonal-continuity theorem; this file fabricates none of those.
