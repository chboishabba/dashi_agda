module DASHI.Biology.Physical.BiologicalParametricStochasticLumpingExact where

------------------------------------------------------------------------
-- Parametric exact rational hidden-marker probabilities. The previous
-- stochastic fixture used weights 1/2 and 1/2 only. Here *any*
-- source-supplied normalized rational branch weights preserve the same
-- future-sufficient code under arbitrary finite mixed action histories.
-- Nonnegative branch weights and exact normalization are required by type.
-- Source-specific calibration remains an additional obligation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _≤_; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Bio
import DASHI.Biology.Physical.BiologicalStochasticFutureLumpingExact as Original
import DASHI.Cognition.PNF.RationalMarkovLumpingFutureExact as Markov

record NormalizedRationalBranches : Set where
  constructor normalizedRationalBranches
  field
    retainWeight : ℚ
    flipWeight : ℚ
    retainNonnegative : 0ℚ ≤ retainWeight
    flipNonnegative : 0ℚ ≤ flipWeight
    sumIsOne : retainWeight + flipWeight ≡ 1ℚ

open NormalizedRationalBranches public

weightedSameValue :
  (weights : NormalizedRationalBranches) (value : ℚ) →
  retainWeight weights * value + flipWeight weights * value ≡ value
weightedSameValue weights value =
  trans
    (solve-∀)
    (trans
      (cong (λ weight → weight * value) (sumIsOne weights))
      (solve-∀))

weightedFineStep :
  NormalizedRationalBranches → Bio.Intervention →
  (Bio.BiologicalState → ℚ) → Bio.BiologicalState → ℚ
weightedFineStep weights action observable state =
  retainWeight weights * observable (Bio.step action state)
  + flipWeight weights *
    observable (Original.flipMarker (Bio.step action state))

weightedCoarseStep :
  Bio.Intervention →
  (Bio.FutureSufficientCode → ℚ) →
  Bio.FutureSufficientCode → ℚ
weightedCoarseStep action observable code =
  observable (Bio.coarseStep action code)

weightedOneStepProjection :
  (weights : NormalizedRationalBranches)
  (action : Bio.Intervention)
  (observable : Bio.FutureSufficientCode → ℚ)
  (state : Bio.BiologicalState) →
  weightedFineStep weights action
    (λ s → observable (Bio.project s)) state
  ≡ weightedCoarseStep action observable (Bio.project state)
weightedOneStepProjection weights action observable state
  rewrite Original.flipPreservesCoarseCode (Bio.step action state)
        | Bio.projectionCommutes action state =
    weightedSameValue weights
      (observable (Bio.coarseStep action (Bio.project state)))

weightedFineWord :
  NormalizedRationalBranches → List Bio.Intervention →
  (Bio.BiologicalState → ℚ) → Bio.BiologicalState → ℚ
weightedFineWord weights [] observable = observable
weightedFineWord weights (a ∷ rest) observable =
  weightedFineStep weights a (weightedFineWord weights rest observable)

weightedCoarseWord :
  List Bio.Intervention →
  (Bio.FutureSufficientCode → ℚ) →
  Bio.FutureSufficientCode → ℚ
weightedCoarseWord [] observable = observable
weightedCoarseWord (a ∷ rest) observable =
  weightedCoarseStep a (weightedCoarseWord rest observable)

arbitraryNormalizedWeightsPreserveAllControlledFutures :
  (weights : NormalizedRationalBranches)
  (actions : List Bio.Intervention)
  (observable : Bio.FutureSufficientCode → ℚ)
  (state : Bio.BiologicalState) →
  weightedFineWord weights actions
    (λ x → observable (Bio.project x)) state
  ≡ weightedCoarseWord actions observable (Bio.project state)
arbitraryNormalizedWeightsPreserveAllControlledFutures weights [] observable state =
  refl
arbitraryNormalizedWeightsPreserveAllControlledFutures
  weights (a ∷ rest) observable state
  rewrite
    arbitraryNormalizedWeightsPreserveAllControlledFutures
      weights rest observable (Bio.step a state)
  | arbitraryNormalizedWeightsPreserveAllControlledFutures
      weights rest observable (Original.flipMarker (Bio.step a state))
  | Original.flipPreservesCoarseCode (Bio.step a state)
  | Bio.projectionCommutes a state =
  weightedSameValue weights
    (weightedCoarseWord rest observable
      (Bio.coarseStep a (Bio.project state)))

------------------------------------------------------------------------
-- Constructive Markov-lumping owner (same native interface as Round-22).
-- Supplies full finite horizon closure, not only selected source words.
------------------------------------------------------------------------

weightedStepFactors :
  (weights : NormalizedRationalBranches)
  (action : Bio.Intervention)
  (observable : Markov.FactoredObservable Bio.project)
  (state : Bio.BiologicalState) →
  weightedFineStep weights action
    (Markov.fineObservable observable) state
  ≡ weightedCoarseStep action
    (Markov.coarseObservable observable)
    (Bio.project state)
weightedStepFactors weights action observable state
  rewrite Markov.factors observable (Bio.step action state)
        | Markov.factors observable
            (Original.flipMarker (Bio.step action state))
        | Original.flipPreservesCoarseCode (Bio.step action state)
        | Bio.projectionCommutes action state =
  weightedSameValue weights
    (Markov.coarseObservable observable
      (Bio.coarseStep action (Bio.project state)))

parametricMarkovLumping :
  (weights : NormalizedRationalBranches)
  (action : Bio.Intervention) →
  Markov.ConstructiveMarkovLumping
    Bio.BiologicalState Bio.FutureSufficientCode
parametricMarkovLumping weights action =
  Markov.constructiveMarkovLumping
    Bio.project
    (weightedFineStep weights action)
    (weightedCoarseStep action)
    (λ observable →
      Markov.factoredObservable
        (weightedFineStep weights action
          (Markov.fineObservable observable))
        (weightedCoarseStep action
          (Markov.coarseObservable observable))
        (weightedStepFactors weights action observable))
    (λ observable state → refl)
    (λ observable code → refl)

parametricAllFiniteHorizonsRemainCoarse :
  (weights : NormalizedRationalBranches)
  (action : Bio.Intervention)
  (horizon : Nat)
  (observable : Bio.FutureSufficientCode → ℚ)
  (state : Bio.BiologicalState) →
  Markov.fineObservable
    (Markov.iterateFactored
      (parametricMarkovLumping weights action) horizon
      (Markov.initialFactoredObservable
        (parametricMarkovLumping weights action) observable)) state
  ≡ Markov.coarseObservable
    (Markov.iterateFactored
      (parametricMarkovLumping weights action) horizon
      (Markov.initialFactoredObservable
        (parametricMarkovLumping weights action) observable))
    (Bio.project state)
parametricAllFiniteHorizonsRemainCoarse weights action horizon observable state =
  Markov.allFiniteHorizonsRemainCoarseFactored
    (parametricMarkovLumping weights action) horizon observable state
