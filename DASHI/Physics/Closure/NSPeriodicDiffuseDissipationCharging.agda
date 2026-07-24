module DASHI.Physics.Closure.NSPeriodicDiffuseDissipationCharging where

open import Agda.Primitive using (Set)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact diffuse-spectrum dissipation-charging theorem.
--
-- The genuinely analytic estimate must charge the diffuse vorticity
-- expenditure to an absorbable part of the viscous dissipation plus a finite
-- remainder.  Once that estimate and the global dissipation budget are
-- supplied, the BKM expenditure bound is pure ordered-additive transitivity.
------------------------------------------------------------------------

record PeriodicDiffuseDissipationChargeInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    vorticityExpenditure : Scalar A
    chargedDissipation : Scalar A
    absorbedDissipation : Scalar A
    diffuseRemainder : Scalar A
    totalDiffuseBudget : Scalar A

    diffuseVorticityCharge :
      _≤_ A vorticityExpenditure
        (_+_ A chargedDissipation diffuseRemainder)

    chargedPartIsAbsorbable :
      _≤_ A chargedDissipation absorbedDissipation

    absorbedDissipationAndRemainderFitBudget :
      _≤_ A
        (_+_ A absorbedDissipation diffuseRemainder)
        totalDiffuseBudget

    VorticityExpenditureFinite : Set

    totalBudgetBoundImpliesFinite :
      _≤_ A vorticityExpenditure totalDiffuseBudget →
      VorticityExpenditureFinite

open PeriodicDiffuseDissipationChargeInputs public

diffuseChargedVorticityBelowTotalBudget :
  ∀ {A : AbsorptionArithmetic} →
  (D : PeriodicDiffuseDissipationChargeInputs A) →
  _≤_ A (vorticityExpenditure D) (totalDiffuseBudget D)
diffuseChargedVorticityBelowTotalBudget {A = A} D =
  ≤-trans A
    (diffuseVorticityCharge D)
    (≤-trans A
      (additionMonotoneRight A (chargedPartIsAbsorbable D))
      (absorbedDissipationAndRemainderFitBudget D))

diffuseDissipationChargeGivesFiniteVorticity :
  ∀ {A : AbsorptionArithmetic} →
  (D : PeriodicDiffuseDissipationChargeInputs A) →
  VorticityExpenditureFinite D
diffuseDissipationChargeGivesFiniteVorticity D =
  totalBudgetBoundImpliesFinite D
    (diffuseChargedVorticityBelowTotalBudget D)

------------------------------------------------------------------------
-- Status: the charging/absorption endpoint is checked.  The frontier estimate
-- is the concrete diffuse inequality producing diffuseVorticityCharge with a
-- cutoff-independent absorbable coefficient and finite remainder.
------------------------------------------------------------------------

diffuseDissipationChargingAssemblyLevel : ProofLevel
diffuseDissipationChargingAssemblyLevel = machineChecked
