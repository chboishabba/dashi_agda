module DASHI.Physics.Closure.NSTriadKNLuoFiniteComparableFilteredBridgeExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- Littlewood--Paley reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Make the physical-space-to-dyadic bridge explicit.  A producer must first
-- dominate the comparable-shell interaction by the complete filtered positive
-- surplus, not merely by its singular near-field part.  Yu's coercive
-- assembly then yields a filtered envelope containing retained diffusion,
-- reservoir, far-field, commutator and localization terms.
--
-- A second producer must bound that entire envelope by C_CC A_q E_q.  Under
-- those two concrete hypotheses the desired comparable-shell estimate follows
-- by transitivity.  This is the exact logical location of the remaining hard
-- analysis; no residual class is silently discarded.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNYuFiniteFilteredSurplusAssemblyExact as Yu

record ComparableToFilteredData : Set where
  constructor comparable-to-filtered-data
  field
    filteredBudget : Yu.FilteredSurplusBudget
    comparableInteraction : ℚ
    comparableDominatedByFilteredSurplus :
      comparableInteraction
      ≤ Yu.totalPositiveSurplus filteredBudget

open ComparableToFilteredData public

comparableBoundedByFilteredEnvelope :
  (bridge : ComparableToFilteredData) →
  comparableInteraction bridge
  ≤ Yu.coerciveSurplusEnvelope (filteredBudget bridge)
comparableBoundedByFilteredEnvelope bridge =
  ℚₚ.≤-trans
    (comparableDominatedByFilteredSurplus bridge)
    (Yu.filteredSurplusAssembly (filteredBudget bridge))

record ComparableCriticalProducer : Set where
  constructor comparable-critical-producer
  field
    bridge : ComparableToFilteredData
    coefficient criticalRoot outputEnergy : ℚ
    completeFilteredEnvelopeBound :
      Yu.coerciveSurplusEnvelope (filteredBudget bridge)
      ≤ coefficient * criticalRoot * outputEnergy

open ComparableCriticalProducer public

comparableCriticalBound :
  (producer : ComparableCriticalProducer) →
  comparableInteraction (bridge producer)
  ≤ coefficient producer
      * criticalRoot producer
      * outputEnergy producer
comparableCriticalBound producer =
  ℚₚ.≤-trans
    (comparableBoundedByFilteredEnvelope (bridge producer))
    (completeFilteredEnvelopeBound producer)
