module DASHI.Core.FiniteStochasticRewardPreservationExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Strengthen the finite stochastic bridge with exact row normalization over a
-- declared finite coarse outcome list and one-step reward preservation.  The
-- representation remains denominator-free: natural transition masses and a
-- common row mass represent rational probabilities when a runtime chooses to
-- divide by that row mass.
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
-- Those works motivate value/reward preservation under behavioural state
-- abstraction.  The exact finite denominator-free lemmas below are DASHI
-- constructions and do not claim their full discounted-value theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Core.FiniteStochasticBisimulationExact as Kernel

sumProjectedMass :
  ∀ {State Action Coarse} →
  Kernel.ProjectedFiniteKernel State Action Coarse →
  Action → State → List Coarse → Nat
sumProjectedMass kernel action state [] = 0
sumProjectedMass kernel action state (coarse ∷ rest) =
  Kernel.transitionMass kernel action state coarse
  + sumProjectedMass kernel action state rest

record NormalizedProjectedKernel
    {State Action Coarse : Set}
    (kernel : Kernel.ProjectedFiniteKernel State Action Coarse) : Set where
  constructor normalizedProjectedKernel
  field
    coarseOutcomes : List Coarse
    rowNormalizes :
      ∀ action state →
      sumProjectedMass kernel action state coarseOutcomes
      ≡ Kernel.rowMass kernel action state

open NormalizedProjectedKernel public

sumMassEqualUnderBisimulation :
  ∀ {State Action Coarse}
    {kernel : Kernel.ProjectedFiniteKernel State Action Coarse} →
  Kernel.KernelBisimulation kernel →
  ∀ {left right} →
  Kernel.project kernel left ≡ Kernel.project kernel right →
  (action : Action) →
  (outcomes : List Coarse) →
  sumProjectedMass kernel action left outcomes
  ≡ sumProjectedMass kernel action right outcomes
sumMassEqualUnderBisimulation bisimulation same action [] = refl
sumMassEqualUnderBisimulation bisimulation same action (coarse ∷ rest)
  rewrite Kernel.sameProjectionSameProjectedKernel bisimulation same action coarse
        | sumMassEqualUnderBisimulation bisimulation same action rest = refl

rowMassEqualUnderNormalizedBisimulation :
  ∀ {State Action Coarse}
    {kernel : Kernel.ProjectedFiniteKernel State Action Coarse} →
  (normalized : NormalizedProjectedKernel kernel) →
  Kernel.KernelBisimulation kernel →
  ∀ {left right} →
  Kernel.project kernel left ≡ Kernel.project kernel right →
  (action : Action) →
  Kernel.rowMass kernel action left ≡ Kernel.rowMass kernel action right
rowMassEqualUnderNormalizedBisimulation normalized bisimulation same action =
  trans
    (sym (rowNormalizes normalized action _))
    (trans
      (sumMassEqualUnderBisimulation bisimulation same action
        (coarseOutcomes normalized))
      (rowNormalizes normalized action _))

weightedProjectedReward :
  ∀ {State Action Coarse} →
  Kernel.ProjectedFiniteKernel State Action Coarse →
  Action → State → (Coarse → Nat) → List Coarse → Nat
weightedProjectedReward kernel action state reward [] = 0
weightedProjectedReward kernel action state reward (coarse ∷ rest) =
  Kernel.transitionMass kernel action state coarse * reward coarse
  + weightedProjectedReward kernel action state reward rest

oneStepRewardNumeratorPreserved :
  ∀ {State Action Coarse}
    {kernel : Kernel.ProjectedFiniteKernel State Action Coarse} →
  Kernel.KernelBisimulation kernel →
  ∀ {left right} →
  Kernel.project kernel left ≡ Kernel.project kernel right →
  (action : Action) →
  (reward : Coarse → Nat) →
  (outcomes : List Coarse) →
  weightedProjectedReward kernel action left reward outcomes
  ≡ weightedProjectedReward kernel action right reward outcomes
oneStepRewardNumeratorPreserved bisimulation same action reward [] = refl
oneStepRewardNumeratorPreserved bisimulation same action reward (coarse ∷ rest)
  rewrite Kernel.sameProjectionSameProjectedKernel bisimulation same action coarse
        | oneStepRewardNumeratorPreserved bisimulation same action reward rest = refl

record StochasticRewardBoundary : Set where
  constructor stochasticRewardBoundary
  field
    normalizationIsRelativeToDeclaredFiniteOutcomeList : Bool
    bisimulationPreservesProjectedTransitionMassVector : Bool
    normalizedBisimulationPreservesRowMass : Bool
    coarseOneStepRewardNumeratorIsPreserved : Bool
    discountedOptimalValueTheoremStillNotClaimedHere : Bool

canonicalStochasticRewardBoundary : StochasticRewardBoundary
canonicalStochasticRewardBoundary =
  stochasticRewardBoundary true true true true true
