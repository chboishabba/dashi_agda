module DASHI.Physics.QuantumSensors.DiamondMCGExistingSchurCovarianceReuseExact where

------------------------------------------------------------------------
-- MCG P1 / W1: reuse the *existing* conditional covariance producer,
-- not a duplicate Schur interface.
--
-- Original mathematical result: Schur complement and conditional covariance.
-- Repository proof owner: BalabanSU2ConditionalCovarianceFormula.
-- Physical study: Omar et al., Science Advances (2026) eaeg5281.
--
-- No physical identification of 'coarse' with environmental interference
-- and no calibration of a diamond detector are asserted here.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
import DASHI.Physics.YangMills.BalabanSU2ConditionalCovarianceFormula as Prior

-- The array rejects the selected coarse nuisance sector *provided* its
-- physical coarse/adjoint maps obey the existing owner's exact hypotheses.
-- This is direct theorem reuse, not a new conditional-covariance formula.
arrayFilteredCoarseModeIsZero :
  ∀ {f c} {Fine : Set f} {Coarse : Set c}
    (model : Prior.ConditionalCovarianceData Fine Coarse)
    (source : Fine) →
    Prior.average model (Prior.conditionalCovariance model source)
      ≡ Prior.coarseZero model
arrayFilteredCoarseModeIsZero =
  Prior.conditionalCovarianceConstraint

-- A lifted nuisance mode is entirely rejected under the owner's additional
-- propagator/lift compatibility condition. Failure of that condition must
-- remain a visible obstruction, not an implicit calibration assumption.
arrayFilteredLiftedModeIsZero :
  ∀ {f c} {Fine : Set f} {Coarse : Set c}
    (model : Prior.ConditionalCovarianceData Fine Coarse)
    (fineZero : Fine)
    (subtractSelf : ∀ value →
       Prior.fineSubtract model value value ≡ fineZero)
    (propagatorLifted : ∀ coarse →
      Prior.propagator model (Prior.averageStar model coarse)
        ≡ Prior.constrainedLift model
          (Prior.average model
            (Prior.propagator model (Prior.averageStar model coarse))))
    (coarse : Coarse) →
    Prior.conditionalCovariance model
      (Prior.averageStar model coarse) ≡ fineZero
arrayFilteredLiftedModeIsZero model fineZero subtractSelf propagatorLifted =
  Prior.conditionalCovarianceKillsLiftedSource
    model fineZero subtractSelf propagatorLifted

-- IMPORTANT NEGATIVE CONTROL: if a *cardiac signal* lies in the same lifted
-- coarse sector, the exact same theorem erases it. This prevents asserting
-- that suppression of nuisance noise alone improves detectability.
arrayCardiacModeCanBeErased :
  ∀ {f c} {Fine : Set f} {Coarse : Set c}
    (model : Prior.ConditionalCovarianceData Fine Coarse)
    (fineZero : Fine)
    (subtractSelf : ∀ value →
       Prior.fineSubtract model value value ≡ fineZero)
    (propagatorLifted : ∀ coarse →
      Prior.propagator model (Prior.averageStar model coarse)
        ≡ Prior.constrainedLift model
          (Prior.average model
            (Prior.propagator model (Prior.averageStar model coarse))))
    (cardiacMode : Coarse) →
    Prior.conditionalCovariance model
      (Prior.averageStar model cardiacMode) ≡ fineZero
arrayCardiacModeCanBeErased =
  arrayFilteredLiftedModeIsZero
