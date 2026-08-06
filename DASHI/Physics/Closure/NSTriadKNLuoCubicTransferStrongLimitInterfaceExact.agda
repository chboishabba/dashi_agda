module DASHI.Physics.Closure.NSTriadKNLuoCubicTransferStrongLimitInterfaceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Roger Temam,
-- "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Shin-ichi Inage,
-- "Conditional Regularity of the Three-Dimensional Navier-Stokes Equations
-- via High-High Triadic Absorption".
-- DOI: 10.20944/preprints202603.1591.v1.
-- Status: non-peer-reviewed preprint.
--
-- DASHI CONTRIBUTION
-- Replace a vague demand for passing a cubic transfer to a limit by an exact
-- three-factor telescope and a finite error interface.  Control of each
-- factor-difference term implies control of the cubic difference.  Linear or
-- weak coefficient convergence alone is deliberately not promoted to these
-- three product bounds.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

cubicDifferenceIdentity :
  ∀ a b c aN bN cN →
  a * b * c - aN * bN * cN
  ≡
  (a - aN) * b * c
  + aN * (b - bN) * c
  + aN * bN * (c - cN)
cubicDifferenceIdentity a b c aN bN cN =
  solve (a ∷ b ∷ c ∷ aN ∷ bN ∷ cN ∷ [])

record CubicTransferErrorBudget : Set where
  constructor cubicTransferErrorBudget
  field
    a b c aApprox bApprox cApprox : ℚ
    firstError secondError thirdError : ℚ

    firstFactorTermBound :
      (a - aApprox) * b * c ≤ firstError

    secondFactorTermBound :
      aApprox * (b - bApprox) * c ≤ secondError

    thirdFactorTermBound :
      aApprox * bApprox * (c - cApprox) ≤ thirdError

open CubicTransferErrorBudget public

cubicTransferDifferenceBound :
  (budget : CubicTransferErrorBudget) →
  a budget * b budget * c budget
    - aApprox budget * bApprox budget * cApprox budget
  ≤ firstError budget + secondError budget + thirdError budget
cubicTransferDifferenceBound budget =
  let
    firstTwo =
      ℚₚ.+-mono-≤
        (firstFactorTermBound budget)
        (secondFactorTermBound budget)

    allThree =
      ℚₚ.+-mono-≤
        firstTwo
        (thirdFactorTermBound budget)

    expanded =
      cubicDifferenceIdentity
        (a budget) (b budget) (c budget)
        (aApprox budget) (bApprox budget) (cApprox budget)
  in
  subst
    (λ lower →
      lower ≤ firstError budget + secondError budget + thirdError budget)
    (sym expanded)
    allThree

exactFactorConvergenceImpliesExactCubicTransfer :
  ∀ a b c aN bN cN →
  a ≡ aN → b ≡ bN → c ≡ cN →
  a * b * c ≡ aN * bN * cN
exactFactorConvergenceImpliesExactCubicTransfer
  a b c .a .b .c refl refl refl = refl

record CubicLimitBoundary : Set where
  constructor cubicLimitBoundary
  field
    weakLinearConvergenceSuppliesThreeProductBounds : Set
    weakLinearConvergenceDoesNotSupplyThreeProductBounds :
      weakLinearConvergenceSuppliesThreeProductBounds → Set

    finiteTelescopeProvesCompactness : Set
    finiteTelescopeDoesNotProveCompactness :
      finiteTelescopeProvesCompactness → Set

canonicalCubicLimitBoundary : CubicLimitBoundary
canonicalCubicLimitBoundary =
  cubicLimitBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
