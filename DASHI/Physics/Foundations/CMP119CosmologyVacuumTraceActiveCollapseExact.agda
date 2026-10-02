{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact where

------------------------------------------------------------------------
-- VACUUM / LORENTZ-INVARIANT BRANCH: TRACE -> ACTIVE STRESS.
--
-- This module contains only exact Lorentzian perfect-fluid algebra.
-- It does NOT assert that the selected CMP119 state is Lorentz invariant,
-- vacuum-like, or that its Euclidean R144 source has been continued.
--
-- For an isotropic Lorentzian stress
--
--   T^mu_nu = diag(-rho,p,p,p)
--
-- define
--
--   Theta  = -rho + 3 p
--   Active =  rho + 3 p.
--
-- Then identically Active = Theta + 2 rho.
--
-- Under the stronger vacuum law p = -rho:
--
--   Theta  = -4 rho
--   Active = -2 rho
--   Theta  = 2 Active.
--
-- Therefore positive vacuum energy gives negative active stress.  The
-- physical programme must still prove that the SAME selected renormalized
-- CMP119 tensor satisfies the vacuum law; isotropy alone is insufficient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; -_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst; sym)

record IsotropicLorentzianStress : Set where
  constructor isotropicStress
  field
    rho : ℚ
    pressure : ℚ

open IsotropicLorentzianStress public

trace : IsotropicLorentzianStress → ℚ
trace stress =
  - rho stress
  + pressure stress + pressure stress + pressure stress

activeStress : IsotropicLorentzianStress → ℚ
activeStress stress =
  rho stress
  + pressure stress + pressure stress + pressure stress

tracePlusTwiceRho :
  ∀ stress →
  activeStress stress
  ≡ trace stress + rho stress + rho stress
tracePlusTwiceRho stress =
  Ring.solve-∀ (rho stress) (pressure stress)

record VacuumLikeLorentzianStress : Set where
  field
    stress : IsotropicLorentzianStress
    pressureIsMinusRho :
      pressure stress ≡ - rho stress

open VacuumLikeLorentzianStress public

vacuumTrace :
  ∀ vacuum →
  trace (stress vacuum)
  ≡ - (rho (stress vacuum) + rho (stress vacuum)
       + rho (stress vacuum) + rho (stress vacuum))
vacuumTrace vacuum
  rewrite pressureIsMinusRho vacuum =
  Ring.solve-∀ (rho (stress vacuum))

vacuumActiveStress :
  ∀ vacuum →
  activeStress (stress vacuum)
  ≡ - (rho (stress vacuum) + rho (stress vacuum))
vacuumActiveStress vacuum
  rewrite pressureIsMinusRho vacuum =
  Ring.solve-∀ (rho (stress vacuum))

vacuumTraceIsTwiceActive :
  ∀ vacuum →
  trace (stress vacuum)
  ≡ activeStress (stress vacuum) + activeStress (stress vacuum)
vacuumTraceIsTwiceActive vacuum
  rewrite pressureIsMinusRho vacuum =
  Ring.solve-∀ (rho (stress vacuum))

vacuumPositiveRhoImpliesActiveNegative :
  ∀ vacuum →
  0ℚ < rho (stress vacuum) →
  activeStress (stress vacuum) < 0ℚ
vacuumPositiveRhoImpliesActiveNegative vacuum rhoPositive =
  let
    pairPositive :
      0ℚ < rho (stress vacuum) + rho (stress vacuum)
    pairPositive = ℚP.+-mono-< rhoPositive rhoPositive

    negativePair :
      - (rho (stress vacuum) + rho (stress vacuum)) < - 0ℚ
    negativePair = ℚP.neg-antimono-< pairPositive
  in
  subst
    (λ left → left < 0ℚ)
    (sym (vacuumActiveStress vacuum))
    (subst
      (λ right →
        - (rho (stress vacuum) + rho (stress vacuum)) < right)
      (Ring.solve [])
      negativePair)

vacuumPositiveRhoImpliesTraceNegative :
  ∀ vacuum →
  0ℚ < rho (stress vacuum) →
  trace (stress vacuum) < 0ℚ
vacuumPositiveRhoImpliesTraceNegative vacuum rhoPositive =
  let
    pairPositive :
      0ℚ < rho (stress vacuum) + rho (stress vacuum)
    pairPositive = ℚP.+-mono-< rhoPositive rhoPositive

    fourPositive :
      0ℚ <
      (rho (stress vacuum) + rho (stress vacuum))
      + (rho (stress vacuum) + rho (stress vacuum))
    fourPositive = ℚP.+-mono-< pairPositive pairPositive

    negativeFour :
      - ((rho (stress vacuum) + rho (stress vacuum))
        + (rho (stress vacuum) + rho (stress vacuum))) < - 0ℚ
    negativeFour = ℚP.neg-antimono-< fourPositive
  in
  subst
    (λ left → left < 0ℚ)
    (sym (vacuumTrace vacuum))
    (subst
      (λ left →
        left
        < - ((rho (stress vacuum) + rho (stress vacuum))
          + (rho (stress vacuum) + rho (stress vacuum))))
      (Ring.solve-∀ (rho (stress vacuum)))
      (subst
        (λ right →
          - ((rho (stress vacuum) + rho (stress vacuum))
            + (rho (stress vacuum) + rho (stress vacuum))) < right)
        (Ring.solve [])
        negativeFour))

------------------------------------------------------------------------
-- FRONTIER FLAGS
------------------------------------------------------------------------

isotropyAloneForcesVacuumEquationOfState : Bool
isotropyAloneForcesVacuumEquationOfState = false

vacuumEquationOfStateCollapsesIndependentT00MagnitudeProblem : Bool
vacuumEquationOfStateCollapsesIndependentT00MagnitudeProblem = true

selectedCMP119VacuumLawStillRequiresPhysicalContinuationWeld : Bool
selectedCMP119VacuumLawStillRequiresPhysicalContinuationWeld = true
