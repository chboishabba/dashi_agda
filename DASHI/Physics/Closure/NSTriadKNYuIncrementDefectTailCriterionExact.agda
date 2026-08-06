module DASHI.Physics.Closure.NSTriadKNYuIncrementDefectTailCriterionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- Coarse-graining reference:
-- Authors: Gregory L. Eyink; Hussein Aluie.
-- Title: "Localness of energy cascade in hydrodynamic turbulence. I.
-- Smooth coarse graining".
-- DOI: 10.1063/1.3266883.
--
-- PURPOSE
-- Formalise the exact terminal implication needed after Yu's differentiated
-- commutator insertion.  The analytic cumulant estimate produces a normalized
-- commutator tail dominated by a derivative-compatible increment-defect tail.
-- If the latter vanishes, then so does the commutator tail, with no change of
-- cutoff or epsilon.
--
-- This is deliberately weaker than claiming that energy implies increment
-- summability.  The missing PDE theorem is now precisely the pointwise
-- domination and vanishing of the increment-defect envelope.
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Limit

record IncrementDefectTailData : Set where
  constructor increment-defect-tail-data
  field
    commutatorTail incrementDefectTail : ℕ → ℚ
    commutatorByIncrementDefect :
      (shell : ℕ) →
      commutatorTail shell ≤ incrementDefectTail shell

open IncrementDefectTailData public

commutatorTailVanishing :
  (dataSet : IncrementDefectTailData) →
  Limit.TendsToZero (incrementDefectTail dataSet) →
  Limit.TendsToZero (commutatorTail dataSet)
commutatorTailVanishing dataSet defectVanishing =
  Limit.interactionDepletionFromCriticalDepletion
    (Limit.critical-to-interaction-data
      (commutatorTail dataSet)
      (incrementDefectTail dataSet)
      (commutatorByIncrementDefect dataSet))
    defectVanishing
