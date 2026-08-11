module DASHI.Physics.Closure.NSTriadKNLuoCriticalProductionGronwallClosureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- This module implements the exact terminal inequality permitted by the
-- highest-alpha route.  For every finite shell/Galerkin cutoff, suppose
--
--   X_out + D <= X_in + N,
--
-- and the positive nonlinear production satisfies
--
--   N <= eta D + A + B X_integrated.
--
-- Then
--
--   X_out + (1-eta) D
--     <= X_in + A + B X_integrated.
--
-- The B integral is an admissible Gronwall reservoir.  In contrast, no
-- uncontrolled sup X or BKM norm is accepted by this interface.  The theorem
-- is parameterized by eta,A,B so a family indexed by both Galerkin and shell
-- cutoffs is uniform definitionally rather than by prose.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _-_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
import Data.Rational.Properties as ℚₚ

record CriticalCutoffBudget (eta additive linear : ℚ) : Set where
  constructor criticalCutoffBudget
  field
    energyIn energyOut diffusion production integratedCritical : ℚ

    finiteCriticalBalance :
      energyOut + diffusion ≤ energyIn + production

    productionTax :
      production
      ≤ eta * diffusion + additive + linear * integratedCritical

open CriticalCutoffBudget public

remainingDiffusionCoefficient : ℚ → ℚ
remainingDiffusionCoefficient eta = 1ℚ - eta

criticalProductionAbsorptionWithGronwallReservoir :
  ∀ {eta additive linear}
    (budget : CriticalCutoffBudget eta additive linear) →
  energyOut budget
    + remainingDiffusionCoefficient eta * diffusion budget
  ≤
  energyIn budget + additive + linear * integratedCritical budget
criticalProductionAbsorptionWithGronwallReservoir
  {eta} {additive} {linear} budget =
  let
    productionInserted :
      energyIn budget + production budget
      ≤
      energyIn budget
        + (eta * diffusion budget
          + additive + linear * integratedCritical budget)
    productionInserted =
      ℚₚ.+-monoʳ-≤ (energyIn budget) (productionTax budget)

    assembled :
      energyOut budget + diffusion budget
      ≤
      energyIn budget
        + (eta * diffusion budget
          + additive + linear * integratedCritical budget)
    assembled =
      ℚₚ.≤-trans (finiteCriticalBalance budget) productionInserted

    shift = - (eta * diffusion budget)
    shifted = ℚₚ.+-monoʳ-≤ shift assembled

    leftMeaning :
      (energyOut budget + diffusion budget) + shift
      ≡
      energyOut budget
        + remainingDiffusionCoefficient eta * diffusion budget
    leftMeaning =
      solve (energyOut budget ∷ diffusion budget ∷ eta ∷ [])

    rightMeaning :
      (energyIn budget
        + (eta * diffusion budget
          + additive + linear * integratedCritical budget))
      + shift
      ≡ energyIn budget + additive + linear * integratedCritical budget
    rightMeaning =
      solve
        ( energyIn budget ∷ diffusion budget ∷ eta
        ∷ additive ∷ linear ∷ integratedCritical budget ∷ [])
  in
  subst
    (λ left →
      left ≤ energyIn budget + additive + linear * integratedCritical budget)
    leftMeaning
    (subst
      (λ right →
        (energyOut budget + diffusion budget) + shift ≤ right)
      rightMeaning
      shifted)

record UniformCriticalCutoffFamily
    (eta additive linear : ℚ) : Set where
  constructor uniformCriticalCutoffFamily
  field
    budgetAt : Nat → Nat → CriticalCutoffBudget eta additive linear

open UniformCriticalCutoffFamily public

uniformFiniteCutoffCriticalEstimate :
  ∀ {eta additive linear}
    (family : UniformCriticalCutoffFamily eta additive linear)
    galerkinCutoff shellCutoff →
  energyOut (budgetAt family galerkinCutoff shellCutoff)
    + remainingDiffusionCoefficient eta
      * diffusion (budgetAt family galerkinCutoff shellCutoff)
  ≤
  energyIn (budgetAt family galerkinCutoff shellCutoff)
    + additive
    + linear
      * integratedCritical (budgetAt family galerkinCutoff shellCutoff)
uniformFiniteCutoffCriticalEstimate family galerkinCutoff shellCutoff =
  criticalProductionAbsorptionWithGronwallReservoir
    (budgetAt family galerkinCutoff shellCutoff)

record StrictCriticalMargin (eta : ℚ) : Set where
  constructor strictCriticalMargin
  field
    etaNonnegative : 0ℚ ≤ eta
    remainingCoefficientNonnegative :
      0ℚ ≤ remainingDiffusionCoefficient eta

open StrictCriticalMargin public

record CriticalClosureAuthorityBoundary : Set where
  constructor criticalClosureAuthorityBoundary
  field
    admissibleGronwallReservoirAlgebraProved : Set
    twoCutoffUniformInterfaceImplemented : Set
    physicalProductionTaxProduced : Set
    strictPositiveMarginProduced : Set
    continuousGronwallTheoremConnected : Set
    infiniteCutoffPassageProved : Set

canonicalCriticalClosureAuthorityBoundary :
  CriticalClosureAuthorityBoundary
canonicalCriticalClosureAuthorityBoundary =
  criticalClosureAuthorityBoundary ⊤ ⊤ ⊥ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
