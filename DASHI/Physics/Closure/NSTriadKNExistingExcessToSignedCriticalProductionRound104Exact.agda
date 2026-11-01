module DASHI.Physics.Closure.NSTriadKNExistingExcessToSignedCriticalProductionRound104Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes Equations
-- in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- ROUND104 / EXISTING EXCESS -> SIGNED-CRITICAL-PRODUCTION WELD
--
-- The new top-down target asks for
--
--   N <= a D + F,       a < nu,
--
-- on the complete signed critical production.  Rounds96--97 already own the
-- exact dynamic algebra needed for the external-replenishment component:
--
--   Flux + delta D <= nu D + R.
--
-- This module removes the superficial mismatch.  Subtracting delta D gives
--
--   Flux <= (nu-delta) D + R,
--
-- so the retained viscosity in the Round104 compiler is definitionally delta.
--
-- Two existing physical payment branches are wired directly:
--
--  (1) capped supercritical excess -> finite endpoint remainder (Round97);
--  (2) uncapped supercritical occupation -> existing compact-Gamma endpoint
--      remainder (Round96).
--
-- Neither constructor invents a new escape/occupation theorem.  The remaining
-- physical work is the same-object identification of the COMPLETE radial
-- packet critical production with these flux cells, and production of either
-- the non-circular cap or the same-trajectory occupation witness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _-_; -_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact as Signed
import DASHI.Physics.Closure.NSTriadKNSupercriticalExternalExcessOccupationRound96Exact as Excess
import DASHI.Physics.Closure.NSTriadKNSupercriticalExcessCompactGammaWeldRound96Exact as Gamma
import DASHI.Physics.Closure.NSTriadKNCappedExcessFiniteRemainderRound97Exact as Capped
import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption as Absorb

------------------------------------------------------------------------
-- Generic order lemma: strict-margin form -> absorbed-coefficient form.
------------------------------------------------------------------------

strictMarginFormToSignedProductionForm :
  (flux delta dissipation viscosity remainder : ℚ) →
  flux + delta * dissipation
    ≤ viscosity * dissipation + remainder →
  flux ≤ (viscosity - delta) * dissipation + remainder
strictMarginFormToSignedProductionForm
    flux delta dissipation viscosity remainder base =
  let
    shifted :
      (flux + delta * dissipation) - delta * dissipation
      ≤ (viscosity * dissipation + remainder) - delta * dissipation
    shifted = ℚP.+-mono-≤ base ℚP.≤-refl

    leftMeaning :
      (flux + delta * dissipation) - delta * dissipation ≡ flux
    leftMeaning = solve (flux ∷ delta ∷ dissipation ∷ [])

    rightMeaning :
      (viscosity * dissipation + remainder) - delta * dissipation
      ≡ (viscosity - delta) * dissipation + remainder
    rightMeaning =
      solve (viscosity ∷ dissipation ∷ remainder ∷ delta ∷ [])
  in
  subst
    (λ left → left ≤ (viscosity - delta) * dissipation + remainder)
    leftMeaning
    (subst
      (λ right →
        (flux + delta * dissipation) - delta * dissipation ≤ right)
      rightMeaning shifted)

------------------------------------------------------------------------
-- Branch 1: Round97 capped excess -> finite endpoint remainder.
------------------------------------------------------------------------

record CappedCriticalEnergyWeld
    {C threshold excessCap viscosity delta : ℚ}
    (budget : Capped.CappedFluxFiniteRemainderBudget
      C threshold excessCap viscosity delta) : Set where
  constructor capped-critical-energy-weld
  field
    initialCritical terminalCritical : ℚ

    -- Same-object critical energy identity/inequality.  The nonlinear term is
    -- the exact capped external flux owned by the Round97 budget.
    criticalEnergyInequality :
      terminalCritical
        + viscosity * Capped.sumCappedDissipation (Capped.cells budget)
      ≤ initialCritical
        + Capped.sumCappedExternalFlux (Capped.cells budget)

open CappedCriticalEnergyWeld public

cappedBudgetSignedProductionEstimate :
  ∀ {C threshold excessCap viscosity delta}
    (budget : Capped.CappedFluxFiniteRemainderBudget
      C threshold excessCap viscosity delta) →
  Capped.sumCappedExternalFlux (Capped.cells budget)
  ≤ (viscosity - delta)
      * Capped.sumCappedDissipation (Capped.cells budget)
    + Capped.finiteEndpointRemainder budget
cappedBudgetSignedProductionEstimate {viscosity = viscosity} {delta = delta}
    budget =
  strictMarginFormToSignedProductionForm
    (Capped.sumCappedExternalFlux (Capped.cells budget))
    delta
    (Capped.sumCappedDissipation (Capped.cells budget))
    viscosity
    (Capped.finiteEndpointRemainder budget)
    (Capped.cappedFluxStrictlyAbsorbedModuloFiniteEndpointRemainder budget)

cappedExcessBuildsSignedCriticalSlice :
  ∀ {C threshold excessCap viscosity delta}
    {budget : Capped.CappedFluxFiniteRemainderBudget
      C threshold excessCap viscosity delta} →
  CappedCriticalEnergyWeld budget →
  Signed.IntegratedSignedCriticalSlice
cappedExcessBuildsSignedCriticalSlice
    {viscosity = viscosity} {delta = delta} {budget = budget} W =
  Signed.integrated-signed-critical-slice
    (initialCritical W)
    (terminalCritical W)
    (Capped.sumCappedDissipation (Capped.cells budget))
    (Capped.sumCappedExternalFlux (Capped.cells budget))
    (Capped.finiteEndpointRemainder budget)
    viscosity
    (viscosity - delta)
    (criticalEnergyInequality W)
    (cappedBudgetSignedProductionEstimate budget)

cappedExcessRetainsExactStrictMargin :
  ∀ {C threshold excessCap viscosity delta}
    {budget : Capped.CappedFluxFiniteRemainderBudget
      C threshold excessCap viscosity delta}
    (W : CappedCriticalEnergyWeld budget) →
  Signed.retainedViscosity (cappedExcessBuildsSignedCriticalSlice W) ≡ delta
cappedExcessRetainsExactStrictMargin
    {viscosity = viscosity} {delta = delta} W =
  solve (viscosity ∷ delta ∷ [])

------------------------------------------------------------------------
-- Branch 2: Round96 excess occupation -> compact-Gamma endpoint remainder.
------------------------------------------------------------------------

record GammaCriticalEnergyWeld
    (data : Gamma.SupercriticalExcessCompactGammaWeld) : Set where
  constructor gamma-critical-energy-weld
  field
    initialCritical terminalCritical : ℚ

    criticalEnergyInequality :
      terminalCritical
        + Excess.viscosity (Gamma.excessBudget data)
            * Excess.sumDissipation
                (Excess.cells (Gamma.excessBudget data))
      ≤ initialCritical
        + Excess.sumExternalFlux
            (Excess.cells (Gamma.excessBudget data))

open GammaCriticalEnergyWeld public

gammaEndpointRemainder : Gamma.SupercriticalExcessCompactGammaWeld → ℚ
gammaEndpointRemainder data =
  Absorb.initialPotential (Gamma.absorption data)
  + Absorb.remainderConstant (Gamma.absorption data)

gammaBudgetSignedProductionEstimate :
  (data : Gamma.SupercriticalExcessCompactGammaWeld) →
  Excess.sumExternalFlux (Excess.cells (Gamma.excessBudget data))
  ≤
    ( Excess.viscosity (Gamma.excessBudget data)
      - Excess.strictMargin (Gamma.excessBudget data))
      * Excess.sumDissipation (Excess.cells (Gamma.excessBudget data))
    + gammaEndpointRemainder data
gammaBudgetSignedProductionEstimate data =
  strictMarginFormToSignedProductionForm
    (Excess.sumExternalFlux (Excess.cells (Gamma.excessBudget data)))
    (Excess.strictMargin (Gamma.excessBudget data))
    (Excess.sumDissipation (Excess.cells (Gamma.excessBudget data)))
    (Excess.viscosity (Gamma.excessBudget data))
    (gammaEndpointRemainder data)
    (Gamma.externalFluxStrictlyAbsorbedModuloEndpointRemainder data)

gammaOccupationBuildsSignedCriticalSlice :
  {data : Gamma.SupercriticalExcessCompactGammaWeld} →
  GammaCriticalEnergyWeld data →
  Signed.IntegratedSignedCriticalSlice
gammaOccupationBuildsSignedCriticalSlice {data = data} W =
  Signed.integrated-signed-critical-slice
    (initialCritical W)
    (terminalCritical W)
    (Excess.sumDissipation (Excess.cells (Gamma.excessBudget data)))
    (Excess.sumExternalFlux (Excess.cells (Gamma.excessBudget data)))
    (gammaEndpointRemainder data)
    (Excess.viscosity (Gamma.excessBudget data))
    ( Excess.viscosity (Gamma.excessBudget data)
      - Excess.strictMargin (Gamma.excessBudget data))
    (criticalEnergyInequality W)
    (gammaBudgetSignedProductionEstimate data)

gammaOccupationRetainsExactStrictMargin :
  {data : Gamma.SupercriticalExcessCompactGammaWeld}
  (W : GammaCriticalEnergyWeld data) →
  Signed.retainedViscosity (gammaOccupationBuildsSignedCriticalSlice W)
  ≡ Excess.strictMargin (Gamma.excessBudget data)
gammaOccupationRetainsExactStrictMargin {data = data} W =
  solve
    ( Excess.viscosity (Gamma.excessBudget data)
    ∷ Excess.strictMargin (Gamma.excessBudget data) ∷ [])

round104CappedExcessFeedsSignedCriticalCompiler : Bool
round104CappedExcessFeedsSignedCriticalCompiler = true

round104CompactGammaOccupationFeedsSignedCriticalCompiler : Bool
round104CompactGammaOccupationFeedsSignedCriticalCompiler = true

-- This is now the actual dynamical frontier inside theorem #2: identify the
-- complete critical packet layer-cake with these physical external-flux cells
-- and prove that every adverse cell is paid by one of the two already-wired
-- branches, uniformly in Galerkin cutoff.
round104PhysicalCompleteFluxExcessCoverageClosed : Bool
round104PhysicalCompleteFluxExcessCoverageClosed = false

round104CappedExcessFeedsSignedCriticalCompilerIsTrue :
  round104CappedExcessFeedsSignedCriticalCompiler ≡ true
round104CappedExcessFeedsSignedCriticalCompilerIsTrue = refl

round104CompactGammaOccupationFeedsSignedCriticalCompilerIsTrue :
  round104CompactGammaOccupationFeedsSignedCriticalCompiler ≡ true
round104CompactGammaOccupationFeedsSignedCriticalCompilerIsTrue = refl

round104PhysicalCompleteFluxExcessCoverageClosedIsFalse :
  round104PhysicalCompleteFluxExcessCoverageClosed ≡ false
round104PhysicalCompleteFluxExcessCoverageClosedIsFalse = refl