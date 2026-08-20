module DASHI.Core.FiniteProjectedKernelDiscrepancyExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Supply a quantitative finite projected-kernel discrepancy between the exact
-- zero-bisimulation theorem and full probabilistic bisimulation metrics.  The
-- discrepancy is denominator-free L1 distance between transition-mass vectors
-- on a declared coarse outcome list.
--
-- REFERENCES / MOTIVATION
--
-- Norman Ferns, Prakash Panangaden, Doina Precup,
-- "Metrics for Finite Markov Decision Processes", UAI 2004, pp. 162-169.
--
-- Norman Ferns, Prakash Panangaden, Doina Precup,
-- "Bisimulation Metrics for Continuous Markov Decision Processes",
-- SIAM Journal on Computing 40(6), 2011, 1662-1714.
-- DOI: 10.1137/10080484X.
--
-- The full Ferns-Panangaden-Precup metric couples rewards and transition laws.
-- This module proves only the exact finite projected transition-vector layer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_≤_; z≤n)

import DASHI.Core.FiniteStochasticBisimulationExact as Kernel

natAbsDiff : Nat → Nat → Nat
natAbsDiff zero right = right
natAbsDiff left zero = left
natAbsDiff (suc left) (suc right) = natAbsDiff left right

natAbsDiffSelfZero : ∀ value → natAbsDiff value value ≡ zero
natAbsDiffSelfZero zero = refl
natAbsDiffSelfZero (suc value) = natAbsDiffSelfZero value

projectedKernelL1Gap :
  ∀ {State Action Coarse} →
  Kernel.ProjectedFiniteKernel State Action Coarse →
  Action → State → State → List Coarse → Nat
projectedKernelL1Gap kernel action left right [] = zero
projectedKernelL1Gap kernel action left right (coarse ∷ rest) =
  natAbsDiff
    (Kernel.transitionMass kernel action left coarse)
    (Kernel.transitionMass kernel action right coarse)
  + projectedKernelL1Gap kernel action left right rest

bisimulationHasZeroProjectedKernelGap :
  ∀ {State Action Coarse}
    {kernel : Kernel.ProjectedFiniteKernel State Action Coarse} →
  Kernel.KernelBisimulation kernel →
  ∀ {left right} →
  Kernel.project kernel left ≡ Kernel.project kernel right →
  (action : Action) →
  (outcomes : List Coarse) →
  projectedKernelL1Gap kernel action left right outcomes ≡ zero
bisimulationHasZeroProjectedKernelGap bisimulation same action [] = refl
bisimulationHasZeroProjectedKernelGap bisimulation same action (coarse ∷ rest)
  rewrite Kernel.sameProjectionSameProjectedKernel bisimulation same action coarse
        | natAbsDiffSelfZero (Kernel.transitionMass kernel action right coarse)
        | bisimulationHasZeroProjectedKernelGap bisimulation same action rest = refl

record ProjectedKernelTolerance
    {State Action Coarse : Set}
    (kernel : Kernel.ProjectedFiniteKernel State Action Coarse)
    (epsilon : Nat) : Set where
  constructor projectedKernelTolerance
  field
    outcomes : List Coarse
    withinTolerance :
      ∀ {left right} →
      Kernel.project kernel left ≡ Kernel.project kernel right →
      (action : Action) →
      projectedKernelL1Gap kernel action left right outcomes ≤ epsilon

open ProjectedKernelTolerance public

exactBisimulationSuppliesZeroTolerance :
  ∀ {State Action Coarse}
    {kernel : Kernel.ProjectedFiniteKernel State Action Coarse} →
  (outcomes : List Coarse) →
  Kernel.KernelBisimulation kernel →
  ProjectedKernelTolerance kernel zero
exactBisimulationSuppliesZeroTolerance outcomes bisimulation =
  projectedKernelTolerance outcomes proof
  where
    proof :
      ∀ {left right} →
      Kernel.project kernel left ≡ Kernel.project kernel right →
      (action : Action) →
      projectedKernelL1Gap kernel action left right outcomes ≤ zero
    proof same action
      rewrite bisimulationHasZeroProjectedKernelGap bisimulation same action outcomes = z≤n

record ProjectedKernelDiscrepancyBoundary : Set where
  constructor projectedKernelDiscrepancyBoundary
  field
    discrepancyIsOutcomeListRelative : Bool
    exactBisimulationImpliesZeroDiscrepancy : Bool
    positiveToleranceDoesNotByItselfGiveValueErrorBound : Bool
    denominatorFreeMassGapNeedsNormalizationForProbabilityInterpretation : Bool

canonicalProjectedKernelDiscrepancyBoundary : ProjectedKernelDiscrepancyBoundary
canonicalProjectedKernelDiscrepancyBoundary =
  projectedKernelDiscrepancyBoundary true true true true
