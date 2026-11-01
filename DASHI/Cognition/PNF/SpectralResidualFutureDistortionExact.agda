module DASHI.Cognition.PNF.SpectralResidualFutureDistortionExact where

------------------------------------------------------------------------
-- SPECTRAL / DYNAMICAL RESIDUAL FUTURE DISTORTION
--
-- Dropping modes is safe only relative to a consumer and a dynamical bound.
-- If omitted-mode magnitude upper-bounds consumer distortion and cannot grow
-- under admissible dynamics, every future trace remains bounded by the initial
-- omitted residual.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement

record SpectralResidualApproximation
    (State Action Retained : Set) : Set₁ where
  constructor spectralResidualApproximation
  field
    retain : State → Retained
    step : Action → State → State
    consumerDistortion : State → Nat
    residualMagnitude : State → Nat
    distortionControlledByResidual :
      (state : State) →
      consumerDistortion state ≤ residualMagnitude state
    residualNonIncreasing :
      (action : Action) (state : State) →
      residualMagnitude (step action state) ≤ residualMagnitude state

open SpectralResidualApproximation public

residualTraceNonIncreasing :
  ∀ {State Action Retained}
    (approximation : SpectralResidualApproximation State Action Retained)
    (actions : List Action) (state : State) →
  residualMagnitude approximation
    (Refinement.run (step approximation) actions state)
  ≤ residualMagnitude approximation state
residualTraceNonIncreasing approximation [] state = ≤-refl
residualTraceNonIncreasing approximation (action ∷ actions) state =
  ≤-trans
    (residualTraceNonIncreasing approximation actions
      (step approximation action state))
    (residualNonIncreasing approximation action state)

futureDistortionBoundedByInitialResidual :
  ∀ {State Action Retained}
    (approximation : SpectralResidualApproximation State Action Retained)
    (actions : List Action) (state : State) →
  consumerDistortion approximation
    (Refinement.run (step approximation) actions state)
  ≤ residualMagnitude approximation state
futureDistortionBoundedByInitialResidual approximation actions state =
  ≤-trans
    (distortionControlledByResidual approximation
      (Refinement.run (step approximation) actions state))
    (residualTraceNonIncreasing approximation actions state)

record CertifiedSpectralModeDrop
    {State Action Retained : Set}
    (approximation : SpectralResidualApproximation State Action Retained)
    (state : State)
    (epsilon : Nat) : Set₁ where
  constructor certifiedSpectralModeDrop
  field
    initialResidualWithinTolerance :
      residualMagnitude approximation state ≤ epsilon

open CertifiedSpectralModeDrop public

certifiedModeDropControlsEveryFutureTrace :
  ∀ {State Action Retained}
    {approximation : SpectralResidualApproximation State Action Retained}
    {state : State} {epsilon : Nat} →
  CertifiedSpectralModeDrop approximation state epsilon →
  (actions : List Action) →
  consumerDistortion approximation
    (Refinement.run (step approximation) actions state)
  ≤ epsilon
certifiedModeDropControlsEveryFutureTrace
  {approximation = approximation} {state = state}
  certificate actions =
  ≤-trans
    (futureDistortionBoundedByInitialResidual approximation actions state)
    (initialResidualWithinTolerance certificate)

------------------------------------------------------------------------
-- Concrete regression: a discarded transient mode decays 2 -> 1 -> 0 while
-- the retained code is constant.  The entire future consumer error is therefore
-- certified by the initial residual budget 2.
------------------------------------------------------------------------

data TransientState : Set where residual2 residual1 residual0 : TransientState

data Tick : Set where tick : Tick

data RetainedCode : Set where sameCode : RetainedCode

transientStep : Tick → TransientState → TransientState
transientStep tick residual2 = residual1
transientStep tick residual1 = residual0
transientStep tick residual0 = residual0

transientMagnitude : TransientState → Nat
transientMagnitude residual2 = 2
transientMagnitude residual1 = 1
transientMagnitude residual0 = 0

transientApproximation :
  SpectralResidualApproximation TransientState Tick RetainedCode
transientApproximation = spectralResidualApproximation
  (λ state → sameCode)
  transientStep
  transientMagnitude
  transientMagnitude
  (λ state → ≤-refl)
  nonIncreasing
  where
    nonIncreasing : (action : Tick) (state : TransientState) →
      transientMagnitude (transientStep action state) ≤ transientMagnitude state
    nonIncreasing tick residual2 = s≤s z≤n
    nonIncreasing tick residual1 = z≤n
    nonIncreasing tick residual0 = ≤-refl

initialTransientDropCertified :
  CertifiedSpectralModeDrop transientApproximation residual2 2
initialTransientDropCertified = certifiedSpectralModeDrop ≤-refl

transientDropFutureErrorNeverExceedsTwo :
  (actions : List Tick) →
  consumerDistortion transientApproximation
    (Refinement.run transientStep actions residual2) ≤ 2
transientDropFutureErrorNeverExceedsTwo =
  certifiedModeDropControlsEveryFutureTrace initialTransientDropCertified

------------------------------------------------------------------------
-- Boundary: a physical/spectral producer must prove residualNonIncreasing in
-- its chosen norm and prove that consumer distortion is controlled by that
-- residual.  Neither fact follows from an eigenvalue label alone.
------------------------------------------------------------------------
