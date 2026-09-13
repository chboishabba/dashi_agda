module DASHI.Physics.Closure.NSTriadKNClayForcedBreakdownFormulationRound523Exact where

------------------------------------------------------------------------
-- ROUND523 / SOURCE-EXACT CLAY FORCED-BREAKDOWN FORMULATION
--
-- Source: Charles L. Fefferman, "Existence and Smoothness of the
-- Navier--Stokes Equation", official Clay Mathematics Institute problem
-- description.
--
-- The official problem accepts any one of four statements A-D.  For the
-- present adversarial BIDI we isolate only C and D, the forced-breakdown
-- alternatives, and keep every source condition constructor-distinct.
--
-- C (R^3): smooth divergence-free initial datum + rapid spatial decay;
--          smooth forcing + rapid joint space/time decay;
--          no global physically reasonable smooth bounded-energy solution.
--
-- D (T^3): smooth periodic divergence-free initial datum;
--          smooth periodic forcing + rapid time decay of all derivatives;
--          no global smooth periodic solution.
--
-- Critical firewall:
--
--   finite-time blowup slogan != Clay C/D payment.
--
-- A blowup construction must still be welded to the exact domain, viscosity,
-- initial-data class, forcing class, equation, and no-global-solution consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Source coordinates.
------------------------------------------------------------------------

data ClayBreakdownDomain523 : Set where
  euclideanR3_523 : ClayBreakdownDomain523
  periodicT3_523 : ClayBreakdownDomain523

data ClayBreakdownCoordinate523 : Set where
  positiveViscosity523 : ClayBreakdownCoordinate523
  dimensionThree523 : ClayBreakdownCoordinate523
  smoothDivergenceFreeInitialDatum523 : ClayBreakdownCoordinate523
  rapidInitialSpatialDecay523 : ClayBreakdownCoordinate523
  periodicInitialDatum523 : ClayBreakdownCoordinate523
  smoothForcing523 : ClayBreakdownCoordinate523
  rapidForcingSpaceTimeDecay523 : ClayBreakdownCoordinate523
  periodicForcing523 : ClayBreakdownCoordinate523
  rapidForcingTimeDecay523 : ClayBreakdownCoordinate523
  exactNavierStokesEquation523 : ClayBreakdownCoordinate523
  noGlobalSmoothSolution523 : ClayBreakdownCoordinate523
  boundedEnergyRequirement523 : ClayBreakdownCoordinate523
  periodicSolutionRequirement523 : ClayBreakdownCoordinate523

data ClayBreakdownAlternative523 : Set where
  clayAlternativeC523 : ClayBreakdownAlternative523
  clayAlternativeD523 : ClayBreakdownAlternative523

requiredByC523 : ClayBreakdownCoordinate523 → Bool
requiredByC523 positiveViscosity523 = true
requiredByC523 dimensionThree523 = true
requiredByC523 smoothDivergenceFreeInitialDatum523 = true
requiredByC523 rapidInitialSpatialDecay523 = true
requiredByC523 periodicInitialDatum523 = false
requiredByC523 smoothForcing523 = true
requiredByC523 rapidForcingSpaceTimeDecay523 = true
requiredByC523 periodicForcing523 = false
requiredByC523 rapidForcingTimeDecay523 = false
requiredByC523 exactNavierStokesEquation523 = true
requiredByC523 noGlobalSmoothSolution523 = true
requiredByC523 boundedEnergyRequirement523 = true
requiredByC523 periodicSolutionRequirement523 = false

requiredByD523 : ClayBreakdownCoordinate523 → Bool
requiredByD523 positiveViscosity523 = true
requiredByD523 dimensionThree523 = true
requiredByD523 smoothDivergenceFreeInitialDatum523 = true
requiredByD523 rapidInitialSpatialDecay523 = false
requiredByD523 periodicInitialDatum523 = true
requiredByD523 smoothForcing523 = true
requiredByD523 rapidForcingSpaceTimeDecay523 = false
requiredByD523 periodicForcing523 = true
requiredByD523 rapidForcingTimeDecay523 = true
requiredByD523 exactNavierStokesEquation523 = true
requiredByD523 noGlobalSmoothSolution523 = true
requiredByD523 boundedEnergyRequirement523 = false
requiredByD523 periodicSolutionRequirement523 = true

------------------------------------------------------------------------
-- Coarse "smooth forced blowup" observation is insufficient.
------------------------------------------------------------------------

data SmoothForcedBlowupObservation523 : Set where
  smoothForcedBlowupObserved523 : SmoothForcedBlowupObservation523

data ClayPaymentAnswer523 : Set where
  paysClayBreakdown523 : ClayPaymentAnswer523
  doesNotYetPayClayBreakdown523 : ClayPaymentAnswer523

record CoarseBlowupWorld523 : Set where
  constructor coarse-blowup-world-523
  field
    observedSurface523 : SmoothForcedBlowupObservation523
    clayPayment523 : ClayPaymentAnswer523

open CoarseBlowupWorld523 public

worldClayPaid523 : CoarseBlowupWorld523
worldClayPaid523 =
  coarse-blowup-world-523 smoothForcedBlowupObserved523 paysClayBreakdown523

worldClayUnpaid523 : CoarseBlowupWorld523
worldClayUnpaid523 =
  coarse-blowup-world-523 smoothForcedBlowupObserved523 doesNotYetPayClayBreakdown523

coarseObserve523 : CoarseBlowupWorld523 → SmoothForcedBlowupObservation523
coarseObserve523 = observedSurface523

coarseClayCollision523 :
  coarseObserve523 worldClayPaid523 ≡ coarseObserve523 worldClayUnpaid523
coarseClayCollision523 = refl

------------------------------------------------------------------------
-- No-go permissions.
------------------------------------------------------------------------

data SmoothForcedBlowupAutomaticallyPaysClay523 : Set where
data SmoothnessAutomaticallyPaysDecay523 : Set where
data SingularBehaviorAutomaticallyPaysNoGlobalSolution523 : Set where

smoothForcedBlowupDoesNotAutomaticallyPayClay523 :
  SmoothForcedBlowupAutomaticallyPaysClay523 → ⊥
smoothForcedBlowupDoesNotAutomaticallyPayClay523 ()

smoothnessDoesNotAutomaticallyPayDecay523 :
  SmoothnessAutomaticallyPaysDecay523 → ⊥
smoothnessDoesNotAutomaticallyPayDecay523 ()

singularBehaviorDoesNotAutomaticallyPayNoGlobalSolution523 :
  SingularBehaviorAutomaticallyPaysNoGlobalSolution523 → ⊥
singularBehaviorDoesNotAutomaticallyPayNoGlobalSolution523 ()

------------------------------------------------------------------------
-- Ledger.
------------------------------------------------------------------------

round523ClayForcedAlternativesSeparated : Bool
round523ClayForcedAlternativesSeparated = true

round523SmoothnessEqualsClayAdmissibility : Bool
round523SmoothnessEqualsClayAdmissibility = false

round523BlowupSloganEqualsNoGlobalSolution : Bool
round523BlowupSloganEqualsNoGlobalSolution = false

round523ClayPromotion : Bool
round523ClayPromotion = false

round523ClayForcedAlternativesSeparatedIsTrue :
  round523ClayForcedAlternativesSeparated ≡ true
round523ClayForcedAlternativesSeparatedIsTrue = refl

round523SmoothnessEqualsClayAdmissibilityIsFalse :
  round523SmoothnessEqualsClayAdmissibility ≡ false
round523SmoothnessEqualsClayAdmissibilityIsFalse = refl

round523BlowupSloganEqualsNoGlobalSolutionIsFalse :
  round523BlowupSloganEqualsNoGlobalSolution ≡ false
round523BlowupSloganEqualsNoGlobalSolutionIsFalse = refl

round523ClayPromotionIsFalse : round523ClayPromotion ≡ false
round523ClayPromotionIsFalse = refl
