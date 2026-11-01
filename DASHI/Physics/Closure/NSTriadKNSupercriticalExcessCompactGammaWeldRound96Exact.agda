module DASHI.Physics.Closure.NSTriadKNSupercriticalExcessCompactGammaWeldRound96Exact where

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
-- ROUND96 / DIRECT COMPACT-GAMMA WELD
--
-- Round96 has reduced external replenishment to
--
--   R_ext + delta D <= nu D + X_ext,
--
-- where X_ext is exactly the finite supercritical critical-amplitude excess
--
--   X_ext = C sum_q D_q X_q.
--
-- The existing compact-Gamma absorption theorem already proves
--
--   marginEscape <= initialPotential + remainderConstant.
--
-- Therefore no second residence/phase/spectral-gap framework is required.
-- If the physical excess is charged to that SAME escape margin, then both
--
--   X_ext <= initialPotential + remainderConstant
--
-- and the external-flux inequality with this fixed endpoint remainder follow
-- by transitivity.  The one source-facing analytic field is consequently the
-- occupation statement `supercriticalExcessPaidByEscape`; everything in this
-- file is exact finite ordered-rational assembly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption as Absorb
import DASHI.Physics.Closure.NSTriadKNIntegratedDangerOccupationWeldRound92Exact as Weld92
import DASHI.Physics.Closure.NSTriadKNSupercriticalExternalExcessOccupationRound96Exact as Excess

record SupercriticalExcessCompactGammaWeld : Set₁ where
  constructor supercritical-excess-compact-gamma-weld
  field
    excessBudget : Excess.ExternalSupercriticalExcessOccupationBudget
    absorption : Absorb.CompactGammaAbsorptionInputs
      Weld92.rationalAbsorptionArithmetic

    -- The Round96 excess uses the same physical escape currency as compact
    -- Gamma, or a smaller one.  Equality is not required.
    excessMarginFitsCompactGammaMargin :
      Excess.marginEscape excessBudget
      ≤ Absorb.marginEscape absorption

open SupercriticalExcessCompactGammaWeld public

supercriticalExcessCostFitsCompactGammaMargin :
  (data : SupercriticalExcessCompactGammaWeld) →
  Excess.sumExcessCost (Excess.cells (excessBudget data))
  ≤ Absorb.marginEscape (absorption data)
supercriticalExcessCostFitsCompactGammaMargin data =
  ℚP.≤-trans
    (Excess.supercriticalExcessPaidByEscape (excessBudget data))
    (excessMarginFitsCompactGammaMargin data)

supercriticalExcessCostBoundByEndpointRemainder :
  (data : SupercriticalExcessCompactGammaWeld) →
  Excess.sumExcessCost (Excess.cells (excessBudget data))
  ≤ Absorb.initialPotential (absorption data)
      + Absorb.remainderConstant (absorption data)
supercriticalExcessCostBoundByEndpointRemainder data =
  ℚP.≤-trans
    (supercriticalExcessCostFitsCompactGammaMargin data)
    (Absorb.absorbedReplenishmentBoundsEscapeMargin
      Weld92.rationalAbsorptionArithmetic (absorption data))

externalFluxStrictlyAbsorbedModuloEndpointRemainder :
  (data : SupercriticalExcessCompactGammaWeld) →
  Excess.sumExternalFlux (Excess.cells (excessBudget data))
    + Excess.strictMargin (excessBudget data)
        * Excess.sumDissipation (Excess.cells (excessBudget data))
  ≤ Excess.viscosity (excessBudget data)
        * Excess.sumDissipation (Excess.cells (excessBudget data))
    + (Absorb.initialPotential (absorption data)
        + Absorb.remainderConstant (absorption data))
externalFluxStrictlyAbsorbedModuloEndpointRemainder data =
  let
    base = Excess.finiteExternalFluxAbsorbedModuloSupercriticalExcess
      (Excess.nonlinearConstantNonnegative (excessBudget data))
      (Excess.viscosityHeadroom (excessBudget data))
      (Excess.cells (excessBudget data))
    endpoint = supercriticalExcessCostBoundByEndpointRemainder data
    replaceExcess = ℚP.+-mono-≤ ℚP.≤-refl endpoint
  in
  ℚP.≤-trans base replaceExcess

round96SupercriticalExcessUsesExistingCompactGammaMargin : Bool
round96SupercriticalExcessUsesExistingCompactGammaMargin = true

round96ExternalFluxStrictAbsorptionFromExcessOccupation : Bool
round96ExternalFluxStrictAbsorptionFromExcessOccupation = true

round96AdditionalPhaseEscapeTheoremRequired : Bool
round96AdditionalPhaseEscapeTheoremRequired = false

round96SupercriticalExcessUsesExistingCompactGammaMarginIsTrue :
  round96SupercriticalExcessUsesExistingCompactGammaMargin ≡ true
round96SupercriticalExcessUsesExistingCompactGammaMarginIsTrue = refl

round96ExternalFluxStrictAbsorptionFromExcessOccupationIsTrue :
  round96ExternalFluxStrictAbsorptionFromExcessOccupation ≡ true
round96ExternalFluxStrictAbsorptionFromExcessOccupationIsTrue = refl

round96AdditionalPhaseEscapeTheoremRequiredIsFalse :
  round96AdditionalPhaseEscapeTheoremRequired ≡ false
round96AdditionalPhaseEscapeTheoremRequiredIsFalse = refl
