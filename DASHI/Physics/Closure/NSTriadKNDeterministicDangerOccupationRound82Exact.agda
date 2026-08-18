module DASHI.Physics.Closure.NSTriadKNDeterministicDangerOccupationRound82Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CALIBRATION
--
-- F. G. Foster,
-- "On the Stochastic Matrices Associated with Certain Queuing Processes",
-- Annals of Mathematical Statistics 24 (1953), 355--360.
-- Historical article; no DOI is asserted here.
--
-- Sean P. Meyn; Richard L. Tweedie,
-- "Markov Chains and Stochastic Stability", 2nd ed., Cambridge University
-- Press, 2009. DOI: 10.1017/CBO9780511626630.
--
-- Roger Temam,
-- "Infinite-Dimensional Dynamical Systems in Mechanics and Physics", 2nd ed.,
-- Springer, 1997. DOI: 10.1007/978-1-4612-0645-3.
--
-- AUTHORITY BOUNDARY
--
-- Foster--Lyapunov theory calibrates the *shape* "drift/escape pays occupation".
-- No stochastic recurrence, expectation, Markov property, invariant measure,
-- or probabilistic hitting-time theorem is imported into Navier--Stokes.
-- The result below is a purely deterministic adapter to the repository's
-- already-proved compact-Gamma replenishment theorem.
--
-- ROUND82 / DETERMINISTIC OCCUPATION FORM
--
-- The physical theorem need not prove pointwise Bdot <= -c at every dangerous
-- instant.  It is enough to prove on the selected interval that
--
--   dangerCost * dangerousResidence <= marginEscape,
--
-- after the absorbable portion of escape/replenishment has been split off.
-- Existing compact-Gamma algebra then gives
--
--   dangerCost * dangerousResidence
--       <= initialPotential + remainderConstant.
--
-- This is exactly the occupation estimate consumed downstream and permits
-- intermittent positive Bdot inside a dangerous interval.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption as Absorb

record AbsorptionProductArithmetic
    (A : Absorb.AbsorptionArithmetic) : Set₁ where
  field
    _*_ : Absorb.Scalar A → Absorb.Scalar A → Absorb.Scalar A

open AbsorptionProductArithmetic public

record DeterministicDangerOccupationInputs
    (A : Absorb.AbsorptionArithmetic)
    (P : AbsorptionProductArithmetic A) : Set₁ where
  field
    absorption : Absorb.CompactGammaAbsorptionInputs A
    dangerCost dangerousResidence : Absorb.Scalar A

    dangerOccupationConsumesEscapeMargin :
      Absorb._≤_ A
        (_*_ P dangerCost dangerousResidence)
        (Absorb.marginEscape absorption)

open DeterministicDangerOccupationInputs public

deterministicDangerOccupationAsAbsorbedResidence :
  ∀ {A : Absorb.AbsorptionArithmetic}
    {P : AbsorptionProductArithmetic A} →
  (I : DeterministicDangerOccupationInputs A P) →
  Absorb.CompactGammaAbsorbedResidenceInputs A
deterministicDangerOccupationAsAbsorbedResidence {P = P} I = record
  { Absorb.absorptionInputs = absorption I
  ; Absorb.dangerousResidenceExpenditure =
      _*_ P (dangerCost I) (dangerousResidence I)
  ; Absorb.dangerousResidenceConsumesEscapeMargin =
      dangerOccupationConsumesEscapeMargin I
  }

deterministicDangerOccupationBound :
  ∀ {A : Absorb.AbsorptionArithmetic}
    {P : AbsorptionProductArithmetic A} →
  (I : DeterministicDangerOccupationInputs A P) →
  Absorb._≤_ A
    (_*_ P (dangerCost I) (dangerousResidence I))
    (Absorb._+_ A
      (Absorb.initialPotential (absorption I))
      (Absorb.remainderConstant (absorption I)))
deterministicDangerOccupationBound {A = A} I =
  Absorb.absorbedCompactGammaReplenishmentBoundsResidence A
    (deterministicDangerOccupationAsAbsorbedResidence I)

round82DeterministicOccupationUsesNoStochasticAuthority : Bool
round82DeterministicOccupationUsesNoStochasticAuthority = true

round82PointwiseNegativeDriftRequiredByOccupationTheorem : Bool
round82PointwiseNegativeDriftRequiredByOccupationTheorem = false

round82IntegratedDangerOccupationReducerConstructed : Bool
round82IntegratedDangerOccupationReducerConstructed = true

round82IntegratedDangerOccupationReducerConstructedIsTrue :
  round82IntegratedDangerOccupationReducerConstructed ≡ true
round82IntegratedDangerOccupationReducerConstructedIsTrue = refl
