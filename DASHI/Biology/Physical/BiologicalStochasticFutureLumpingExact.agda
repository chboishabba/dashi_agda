module DASHI.Biology.Physical.BiologicalStochasticFutureLumpingExact where

------------------------------------------------------------------------
-- SYNTHETIC FINITE STOCHASTIC BIOLOGY / FUTURE OBSERVATIONS
--
-- Each controlled step randomizes the intentionally inert chromatin marker
-- by a fair two-branch transition.  The observed five-coordinate phenotype
-- code is exactly Markov-lumpable.  This is a genuine stochastic *operator*
-- over rational probabilities, not merely a deterministic step relabelled.
--
-- No claim of empirical chromatin invariance or calibrated transition rates.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Bio
import DASHI.Cognition.PNF.RationalMarkovLumpingFutureExact as Markov

flipMarker : Bio.BiologicalState → Bio.BiologicalState
flipMarker (Bio.biologicalState g false h j e p) =
  Bio.biologicalState g true h j e p
flipMarker (Bio.biologicalState g true h j e p) =
  Bio.biologicalState g false h j e p

flipPreservesCoarseCode :
  (x : Bio.BiologicalState) →
  Bio.project (flipMarker x) ≡ Bio.project x
flipPreservesCoarseCode (Bio.biologicalState g false h j e p) = refl
flipPreservesCoarseCode (Bio.biologicalState g true h j e p) = refl

halfPlusHalf :
  (x : ℚ) → (½ * x) + (½ * x) ≡ x
halfPlusHalf x = solve-∀

halfMarkerStep :
  Bio.Intervention → (Bio.BiologicalState → ℚ) →
  Bio.BiologicalState → ℚ
halfMarkerStep action observable x =
  ½ * observable (Bio.step action x)
  + ½ * observable (flipMarker (Bio.step action x))

coarseMarkovStep :
  Bio.Intervention → (Bio.FutureSufficientCode → ℚ) →
  Bio.FutureSufficientCode → ℚ
coarseMarkovStep action observable code =
  observable (Bio.coarseStep action code)

constantOnePreserved :
  (a : Bio.Intervention) (x : Bio.BiologicalState) →
  halfMarkerStep a (λ state → 1ℚ) x ≡ 1ℚ
constantOnePreserved a x = halfPlusHalf 1ℚ

halfMarkerStepFactors :
  (a : Bio.Intervention)
  (observable : Markov.FactoredObservable Bio.project)
  (state : Bio.BiologicalState) →
  halfMarkerStep a (Markov.fineObservable observable) state
  ≡ coarseMarkovStep a
      (Markov.coarseObservable observable)
      (Bio.project state)
halfMarkerStepFactors a observable x
  rewrite Markov.factors observable (Bio.step a x)
        | Markov.factors observable (flipMarker (Bio.step a x))
        | flipPreservesCoarseCode (Bio.step a x)
        | Bio.projectionCommutes a x =
  halfPlusHalf (Markov.coarseObservable observable
    (Bio.coarseStep a (Bio.project x)))

stochasticBiologicalLumping :
  (a : Bio.Intervention) →
  Markov.ConstructiveMarkovLumping
    Bio.BiologicalState Bio.FutureSufficientCode
stochasticBiologicalLumping action =
  Markov.constructiveMarkovLumping
    Bio.project
    (halfMarkerStep action)
    (coarseMarkovStep action)
    (λ observable →
      Markov.factoredObservable
        (halfMarkerStep action (Markov.fineObservable observable))
        (coarseMarkovStep action (Markov.coarseObservable observable))
        (halfMarkerStepFactors action observable))
    (λ observable state → refl)
    (λ observable coarse → refl)

stochasticOneStepFutureIsCoarse :
  (a : Bio.Intervention)
  (observable : Bio.FutureSufficientCode → ℚ)
  (state : Bio.BiologicalState) →
  halfMarkerStep a (λ x → observable (Bio.project x)) state
  ≡ coarseMarkovStep a observable (Bio.project state)
stochasticOneStepFutureIsCoarse a observable state =
  Markov.oneStepMarkovLumping
    (stochasticBiologicalLumping a) observable state

allStochasticHorizonsRemainCoarse :
  (a : Bio.Intervention)
  (horizon : Nat)
  (observable : Bio.FutureSufficientCode → ℚ)
  (state : Bio.BiologicalState) →
  Markov.fineObservable
    (Markov.iterateFactored
      (stochasticBiologicalLumping a) horizon
      (Markov.initialFactoredObservable
        (stochasticBiologicalLumping a) observable)) state
  ≡ Markov.coarseObservable
    (Markov.iterateFactored
      (stochasticBiologicalLumping a) horizon
      (Markov.initialFactoredObservable
        (stochasticBiologicalLumping a) observable))
    (Bio.project state)
allStochasticHorizonsRemainCoarse a horizon observable state =
  Markov.allFiniteHorizonsRemainCoarseFactored
    (stochasticBiologicalLumping a) horizon observable state
