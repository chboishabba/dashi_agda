module DASHI.Physics.Closure.NSTriadKNIntegratedDangerOccupationToSignedCriticalRound104Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes Equations
-- in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- ROUND104 / ROUND92 DANGER-OCCUPATION DIRECT WELD
--
-- Round92 already proves the integrated signed estimate
--
--   N + delta D <= initialPotential + remainderConstant
--
-- from a same-trajectory danger-cost occupation budget.  The new top-down
-- critical compiler should consume that theorem directly rather than restate it
-- as an independent `N <= aD+F` receipt.
--
-- Algebraically,
--
--   N <= (-delta) D + endpointRemainder.
--
-- Combining with the exact critical energy inequality
--
--   X(T) + nu D <= X(0) + N
--
-- therefore yields
--
--   X(T) + (nu+delta) D <= X(0) + endpointRemainder.
--
-- Thus Round92's integrated mechanism is stronger than merely retaining a
-- fraction of viscosity.  The only missing theorem is physical construction of
-- the signed danger-cost episode from the literal complete critical packet
-- layer-cake; Round92 already marks that physical producer false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact as Signed
import DASHI.Physics.Closure.NSTriadKNIntegratedSignedDangerCostRound92Exact as Cost
import DASHI.Physics.Closure.NSTriadKNIntegratedDangerOccupationWeldRound92Exact as Occupation
import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption as Absorb

record DangerOccupationCriticalEnergyWeld
    {delta : ℚ}
    (data : Occupation.RationalIntegratedDangerOccupation delta) : Set where
  constructor danger-occupation-critical-energy-weld
  field
    viscosity initialCritical terminalCritical : ℚ

    criticalEnergyInequality :
      terminalCritical
        + viscosity
            * Cost.sumDissipation
                (Cost.cells (Occupation.signedBudget data))
      ≤ initialCritical
        + Cost.sumProduction
            (Cost.cells (Occupation.signedBudget data))

open DangerOccupationCriticalEnergyWeld public

occupationEndpointRemainder :
  ∀ {delta} →
  Occupation.RationalIntegratedDangerOccupation delta → ℚ
occupationEndpointRemainder data =
  Absorb.initialPotential (Occupation.absorption data)
  + Absorb.remainderConstant (Occupation.absorption data)

occupationSignedProductionEstimate :
  ∀ {delta}
    (data : Occupation.RationalIntegratedDangerOccupation delta) →
  Cost.sumProduction (Cost.cells (Occupation.signedBudget data))
  ≤ (- delta)
      * Cost.sumDissipation (Cost.cells (Occupation.signedBudget data))
    + occupationEndpointRemainder data
occupationSignedProductionEstimate {delta} data =
  let
    production = Cost.sumProduction (Cost.cells (Occupation.signedBudget data))
    dissipation = Cost.sumDissipation (Cost.cells (Occupation.signedBudget data))
    endpoint = occupationEndpointRemainder data
    base : production + delta * dissipation ≤ endpoint
    base = Occupation.integratedSignedCriticalEstimateFromOccupation data

    shifted :
      (production + delta * dissipation) + (- (delta * dissipation))
      ≤ endpoint + (- (delta * dissipation))
    shifted = ℚP.+-mono-≤ base ℚP.≤-refl

    leftMeaning :
      (production + delta * dissipation) + (- (delta * dissipation))
      ≡ production
    leftMeaning = solve (production ∷ delta ∷ dissipation ∷ [])

    rightMeaning :
      endpoint + (- (delta * dissipation))
      ≡ (- delta) * dissipation + endpoint
    rightMeaning = solve (endpoint ∷ delta ∷ dissipation ∷ [])
  in
  subst
    (λ left → left ≤ (- delta) * dissipation + endpoint)
    leftMeaning
    (subst
      (λ right →
        (production + delta * dissipation) + (- (delta * dissipation)) ≤ right)
      rightMeaning shifted)

dangerOccupationBuildsSignedCriticalSlice :
  ∀ {delta}
    {data : Occupation.RationalIntegratedDangerOccupation delta} →
  DangerOccupationCriticalEnergyWeld data →
  Signed.IntegratedSignedCriticalSlice
dangerOccupationBuildsSignedCriticalSlice {delta} {data} W =
  Signed.integrated-signed-critical-slice
    (initialCritical W)
    (terminalCritical W)
    (Cost.sumDissipation (Cost.cells (Occupation.signedBudget data)))
    (Cost.sumProduction (Cost.cells (Occupation.signedBudget data)))
    (occupationEndpointRemainder data)
    (viscosity W)
    (- delta)
    (criticalEnergyInequality W)
    (occupationSignedProductionEstimate data)

dangerOccupationRetainedViscosityIsNuPlusDelta :
  ∀ {delta}
    {data : Occupation.RationalIntegratedDangerOccupation delta}
    (W : DangerOccupationCriticalEnergyWeld data) →
  Signed.retainedViscosity (dangerOccupationBuildsSignedCriticalSlice W)
  ≡ viscosity W + delta
dangerOccupationRetainedViscosityIsNuPlusDelta {delta} W =
  solve (viscosity W ∷ delta ∷ [])

round104Round92DangerOccupationFeedsCriticalCompiler : Bool
round104Round92DangerOccupationFeedsCriticalCompiler = true

round104PointwiseNegativeCriticalDriftRequired : Bool
round104PointwiseNegativeCriticalDriftRequired = false

round104PhysicalSignedDangerCostEpisodeClosed : Bool
round104PhysicalSignedDangerCostEpisodeClosed =
  Occupation.round92PhysicalSignedDangerCostEpisodeConstructed

round104Round92DangerOccupationFeedsCriticalCompilerIsTrue :
  round104Round92DangerOccupationFeedsCriticalCompiler ≡ true
round104Round92DangerOccupationFeedsCriticalCompilerIsTrue = refl

round104PointwiseNegativeCriticalDriftRequiredIsFalse :
  round104PointwiseNegativeCriticalDriftRequired ≡ false
round104PointwiseNegativeCriticalDriftRequiredIsFalse = refl

round104PhysicalSignedDangerCostEpisodeClosedIsFalse :
  round104PhysicalSignedDangerCostEpisodeClosed ≡ false
round104PhysicalSignedDangerCostEpisodeClosedIsFalse = refl