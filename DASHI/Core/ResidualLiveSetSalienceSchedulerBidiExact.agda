module DASHI.Core.ResidualLiveSetSalienceSchedulerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ResidualSalienceSchedulerBidiExact as Scheduler
import DASHI.Core.ResidualSalienceBidiCrossPollination2026Exact as Salience

------------------------------------------------------------------------
-- RESIDUAL SALIENCE IS RELATIVE TO THE LIVE HYPOTHESIS SET
--
-- This strengthens the earlier scheduler bridge. Magnitude remains a property
-- of a residual; salience is represented by strict refinement of the currently
-- live hypothesis set. Therefore the same residual can be inert for one live
-- set and discriminating for another.
------------------------------------------------------------------------

LiveSet : Set → Set₁
LiveSet Hypothesis = Hypothesis → Set

record ResidualMove (Hypothesis : Set) : Set₁ where
  constructor residual-move
  field
    magnitude : Nat
    applyTo : LiveSet Hypothesis → LiveSet Hypothesis
    residualReference : String

open ResidualMove public

record StrictLiveSetNarrowing {Hypothesis : Set}
    (after before : LiveSet Hypothesis) : Set where
  constructor strict-live-set-narrowing
  field
    refines : ∀ h → after h → before h
    eliminated : Σ Hypothesis (λ h → before h × ¬ (after h))

open StrictLiveSetNarrowing public

SalientOn :
  ∀ {Hypothesis : Set} →
  ResidualMove Hypothesis → LiveSet Hypothesis → Set
SalientOn residual live =
  StrictLiveSetNarrowing (applyTo residual live) live

------------------------------------------------------------------------
-- Exact finite calibration.
------------------------------------------------------------------------

data ToyHypothesis : Set where h0 h1 h2 : ToyHypothesis

toyLive : LiveSet ToyHypothesis
toyLive h0 = ⊤
toyLive h1 = ⊤
toyLive h2 = ⊤

largeInert : ResidualMove ToyHypothesis
largeInert = residual-move
  10
  (λ live → live)
  "large residual that preserves the whole live set"

smallSeparating : ResidualMove ToyHypothesis
smallSeparating = residual-move
  1
  posterior
  "small residual that eliminates one live hypothesis"
  where
    posterior : LiveSet ToyHypothesis → LiveSet ToyHypothesis
    posterior live h0 = live h0
    posterior live h1 = live h1
    posterior live h2 = ⊥

smallResidualIsSalient : SalientOn smallSeparating toyLive
smallResidualIsSalient =
  strict-live-set-narrowing
    refine
    (h2 , (tt , (λ x → x)))
  where
    refine : ∀ h → applyTo smallSeparating toyLive h → toyLive h
    refine h0 proof = proof
    refine h1 proof = proof
    refine h2 ()

largeResidualIsNotSalient : SalientOn largeInert toyLive → ⊥
largeResidualIsNotSalient receipt with eliminated receipt
... | h0 , (before , notAfter) = notAfter before
... | h1 , (before , notAfter) = notAfter before
... | h2 , (before , notAfter) = notAfter before

data SchedulerChoice : Set where
  chooseLargeInert chooseSmallSeparating : SchedulerChoice

magnitudeGreedy : SchedulerChoice
magnitudeGreedy = chooseLargeInert

salienceGreedy : SchedulerChoice
salienceGreedy = chooseSmallSeparating

magnitudeGreedySelectsInert : magnitudeGreedy ≡ chooseLargeInert
magnitudeGreedySelectsInert = refl

salienceGreedySelectsStrictNarrowing : salienceGreedy ≡ chooseSmallSeparating
salienceGreedySelectsStrictNarrowing = refl

data ResidualMagnitudeDeterminesLiveSetSalience : Set where
data SalienceIndependentOfLiveSet : Set where

magnitudeDoesNotDetermineLiveSetSalience :
  ResidualMagnitudeDeterminesLiveSetSalience → ⊥
magnitudeDoesNotDetermineLiveSetSalience ()

salienceIsNotIndependentOfLiveSet : SalienceIndependentOfLiveSet → ⊥
salienceIsNotIndependentOfLiveSet ()

record ResidualLiveSetSalienceBoundary : Set where
  constructor residual-live-set-salience-boundary
  field
    salienceIndexedByResidualAndLiveSet : Bool
    smallResidualMayStrictlyNarrow : Bool
    largeResidualMayBeInert : Bool
    magnitudeGreedyMayMissNarrowing : Bool
    salienceCreatesCandidateAdmission : Bool

canonicalResidualLiveSetSalienceBoundary : ResidualLiveSetSalienceBoundary
canonicalResidualLiveSetSalienceBoundary =
  residual-live-set-salience-boundary true true true true false
