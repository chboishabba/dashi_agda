module DASHI.Physics.Closure.NSTriadKNLuoFiniteLowHighSecondMomentBridgeExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Connect the already-proved centered second-moment commutator sum to the
-- corrected critical low--high target.  The paired Taylor cancellation gives
--
--   weighted remainder sum
--     <= curvature * weighted second-moment sum.
--
-- To obtain LH4, a continuum producer must bound that complete second-moment
-- envelope by C_LH A_q E_q with all Bernstein exponents visible.  Once that
-- bound is provided, the desired low--high estimate follows exactly by
-- transitivity.  This module therefore closes the composition while leaving
-- the genuinely analytic exponent estimate explicit.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNLuoFiniteCenteredCommutatorBudgetExact as Centered

record LowHighSecondMomentProducer : Set₁ where
  constructor low-high-second-moment-producer
  field
    centeredBudget : Centered.FiniteCenteredCommutatorBudget
    coefficient criticalRoot outputEnergy : ℚ
    completeSecondMomentCriticalBound :
      Centered.curvature centeredBudget
        * Centered.sumBy
            (Centered.samples centeredBudget)
            Centered.weightedSecondMoment
      ≤ coefficient * criticalRoot * outputEnergy

open LowHighSecondMomentProducer public

lowHighCriticalBound :
  (producer : LowHighSecondMomentProducer) →
  Centered.sumBy
    (Centered.samples (centeredBudget producer))
    Centered.weightedRemainder
  ≤ coefficient producer
      * criticalRoot producer
      * outputEnergy producer
lowHighCriticalBound producer =
  ℚₚ.≤-trans
    (Centered.finiteCenteredSecondMomentBudget
      (centeredBudget producer))
    (completeSecondMomentCriticalBound producer)
