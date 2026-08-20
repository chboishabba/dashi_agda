module DASHI.Core.FiniteStochasticBellmanPreservationExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Move beyond one-step transition equality to the decision quantity used by a
-- finite Bellman backup.  Under normalized projected-kernel bisimulation, two
-- fine states with the same coarse projection have identical action scores for
-- every declared action and every coarse continuation-value function; hence the
-- maximum over any declared finite action list is identical.
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
-- Their theory motivates value preservation/error control.  The theorem below
-- is an exact, finite, denominator-free Bellman-backup result; it is not a claim
-- of the full discounted infinite-horizon metric bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Core.FiniteStochasticBisimulationExact as Kernel
import DASHI.Core.FiniteStochasticRewardPreservationExact as Reward

bellmanNumerator :
  ∀ {State Action Coarse} →
  (kernel : Kernel.ProjectedFiniteKernel State Action Coarse) →
  Reward.NormalizedProjectedKernel kernel →
  (immediate : Coarse → Nat) →
  (continuation : Coarse → Nat) →
  Action → State → Nat
bellmanNumerator kernel normalized immediate continuation action state =
  immediate (Kernel.project kernel state) * Kernel.rowMass kernel action state
  + Reward.weightedProjectedReward kernel action state continuation
      (Reward.coarseOutcomes normalized)

bellmanNumeratorPreserved :
  ∀ {State Action Coarse}
    {kernel : Kernel.ProjectedFiniteKernel State Action Coarse} →
  (normalized : Reward.NormalizedProjectedKernel kernel) →
  (bisimulation : Kernel.KernelBisimulation kernel) →
  (immediate continuation : Coarse → Nat) →
  ∀ {left right} →
  (same : Kernel.project kernel left ≡ Kernel.project kernel right) →
  (action : Action) →
  bellmanNumerator kernel normalized immediate continuation action left
  ≡ bellmanNumerator kernel normalized immediate continuation action right
bellmanNumeratorPreserved {kernel = kernel} normalized bisimulation
  immediate continuation {left} {right} same action
  rewrite same
        | Reward.rowMassEqualUnderNormalizedBisimulation
            normalized bisimulation same action
        | Reward.oneStepRewardNumeratorPreserved
            bisimulation same action continuation (Reward.coarseOutcomes normalized) = refl

actionScoreList :
  ∀ {State Action Coarse} →
  (kernel : Kernel.ProjectedFiniteKernel State Action Coarse) →
  Reward.NormalizedProjectedKernel kernel →
  (immediate continuation : Coarse → Nat) →
  List Action → State → List Nat
actionScoreList kernel normalized immediate continuation [] state = []
actionScoreList kernel normalized immediate continuation (action ∷ rest) state =
  bellmanNumerator kernel normalized immediate continuation action state
  ∷ actionScoreList kernel normalized immediate continuation rest state

actionScoreListPreserved :
  ∀ {State Action Coarse}
    {kernel : Kernel.ProjectedFiniteKernel State Action Coarse} →
  (normalized : Reward.NormalizedProjectedKernel kernel) →
  (bisimulation : Kernel.KernelBisimulation kernel) →
  (immediate continuation : Coarse → Nat) →
  (actions : List Action) →
  ∀ {left right} →
  Kernel.project kernel left ≡ Kernel.project kernel right →
  actionScoreList kernel normalized immediate continuation actions left
  ≡ actionScoreList kernel normalized immediate continuation actions right
actionScoreListPreserved normalized bisimulation immediate continuation [] same = refl
actionScoreListPreserved {kernel = kernel} normalized bisimulation
  immediate continuation (action ∷ rest) same
  rewrite bellmanNumeratorPreserved normalized bisimulation
            immediate continuation same action
        | actionScoreListPreserved normalized bisimulation
            immediate continuation rest same = refl

maxNat : Nat → Nat → Nat
maxNat zero right = right
maxNat left zero = left
maxNat (suc left) (suc right) = suc (maxNat left right)

maxList : List Nat → Nat
maxList [] = zero
maxList (value ∷ rest) = maxNat value (maxList rest)

finiteActionOptimalNumeratorPreserved :
  ∀ {State Action Coarse}
    {kernel : Kernel.ProjectedFiniteKernel State Action Coarse} →
  (normalized : Reward.NormalizedProjectedKernel kernel) →
  (bisimulation : Kernel.KernelBisimulation kernel) →
  (immediate continuation : Coarse → Nat) →
  (actions : List Action) →
  ∀ {left right} →
  Kernel.project kernel left ≡ Kernel.project kernel right →
  maxList (actionScoreList kernel normalized immediate continuation actions left)
  ≡ maxList (actionScoreList kernel normalized immediate continuation actions right)
finiteActionOptimalNumeratorPreserved normalized bisimulation
  immediate continuation actions same =
  cong maxList
    (actionScoreListPreserved normalized bisimulation
      immediate continuation actions same)

record BellmanPreservationBoundary : Set where
  constructor bellmanPreservationBoundary
  field
    everyDeclaredActionScoreIsPreserved : Bool
    finiteActionMaximumIsPreserved : Bool
    continuationValueMayBeAnyCoarseNatFunction : Bool
    theoremIsExactNotApproximate : Bool
    infiniteHorizonDiscountMetricBoundNotClaimed : Bool

canonicalBellmanPreservationBoundary : BellmanPreservationBoundary
canonicalBellmanPreservationBoundary =
  bellmanPreservationBoundary true true true true true
