module DASHI.Core.ContrastiveInterventionResponseExact where

------------------------------------------------------------------------
-- CONTRASTIVE INTERVENTION RESPONSE
--
-- Generic companion to ContrastiveHistoryResidualExact.  A response is not
-- represented as a post-state alone, but as a contrast between a declared
-- control/baseline observation and an intervention-conditioned observation:
--
--   response(state , intervention)
--     = contrast(observe(control state), observe(intervention state)).
--
-- This supports perturbational / shiftability experiments without assuming
-- that baseline observation already determines intervention susceptibility.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.ObserverRefinementLatticeExact as Observer

ContrastiveInterventionResponse :
  ∀ {State Intervention Observation Response : Set} →
  (State → Observation) →
  (Intervention → State → State) →
  Intervention →
  (Observation → Observation → Response) →
  State → Intervention → Response
ContrastiveInterventionResponse observe intervene control contrast state intervention =
  contrast
    (observe (intervene control state))
    (observe (intervene intervention state))

baselineObserver :
  ∀ {State Intervention Observation : Set} →
  (State → Observation) →
  (Intervention → State → State) →
  Intervention →
  Observer.Observer State Observation
baselineObserver observe intervene control state =
  observe (intervene control state)

baselineAndResponseObserver :
  ∀ {State Intervention Observation Response : Set} →
  (State → Observation) →
  (Intervention → State → State) →
  Intervention →
  (Observation → Observation → Response) →
  Intervention →
  Observer.Observer State (Observation × Response)
baselineAndResponseObserver observe intervene control contrast intervention =
  Observer.pairObserver
    (baselineObserver observe intervene control)
    (λ state →
      ContrastiveInterventionResponse
        observe intervene control contrast state intervention)

responseCollisionGivesStrictBaselineRefinement :
  ∀ {State Intervention Observation Response : Set}
    (observe : State → Observation)
    (intervene : Intervention → State → State)
    (control : Intervention)
    (contrast : Observation → Observation → Response)
    (intervention : Intervention)
    (x y : State) →
  baselineObserver observe intervene control x
    ≡ baselineObserver observe intervene control y →
  (ContrastiveInterventionResponse
      observe intervene control contrast x intervention
    ≡ ContrastiveInterventionResponse
      observe intervene control contrast y intervention → ⊥) →
  Observer.StrictRefinement
    (baselineObserver observe intervene control)
    (baselineAndResponseObserver
      observe intervene control contrast intervention)
responseCollisionGivesStrictBaselineRefinement
  observe intervene control contrast intervention x y
  sameBaseline differentResponse =
  Observer.strictPairRefinement
    (baselineObserver observe intervene control)
    (λ state →
      ContrastiveInterventionResponse
        observe intervene control contrast state intervention)
    x y sameBaseline differentResponse

ResponseDescendsThroughBaseline :
  ∀ {State Intervention Observation Response : Set} →
  (State → Observation) →
  (Intervention → State → State) →
  Intervention →
  (Observation → Observation → Response) →
  Intervention →
  Set
ResponseDescendsThroughBaseline {Observation = Observation} {Response = Response}
  observe intervene control contrast intervention =
  Σ (Observation → Response)
    (λ reconstruct →
      ∀ state →
      reconstruct (baselineObserver observe intervene control state)
      ≡ ContrastiveInterventionResponse
          observe intervene control contrast state intervention)

responseCollisionBlocksBaselineDescent :
  ∀ {State Intervention Observation Response : Set}
    {observe : State → Observation}
    {intervene : Intervention → State → State}
    {control : Intervention}
    {contrast : Observation → Observation → Response}
    {intervention : Intervention}
    {x y : State} →
  baselineObserver observe intervene control x
    ≡ baselineObserver observe intervene control y →
  (ContrastiveInterventionResponse
      observe intervene control contrast x intervention
    ≡ ContrastiveInterventionResponse
      observe intervene control contrast y intervention → ⊥) →
  ResponseDescendsThroughBaseline
    observe intervene control contrast intervention →
  ⊥
responseCollisionBlocksBaselineDescent {x = x} {y = y}
  sameBaseline differentResponse descent =
  differentResponse
    (trans
      (sym (commutes x))
      (trans
        (cong reconstruct sameBaseline)
        (commutes y)))
  where
    reconstruct = proj₁ descent
    commutes = proj₂ descent

------------------------------------------------------------------------
-- A useful intervention response is not automatically a complete latent-state
-- observer.  This boundary prevents perturbational separation from being
-- promoted into identity of mechanism or complete state reconstruction.
------------------------------------------------------------------------

record ContrastiveInterventionBoundary : Set where
  constructor contrastiveInterventionBoundary
  field
    baselineAndInterventionComparisonRepresentable : Bool
    baselineAndInterventionComparisonRepresentableIsTrue :
      baselineAndInterventionComparisonRepresentable ≡ true

    equalBaselineCanHideDifferentResponse : Bool
    equalBaselineCanHideDifferentResponseIsTrue :
      equalBaselineCanHideDifferentResponse ≡ true

    baselineAutomaticallyDeterminesResponse : Bool
    baselineAutomaticallyDeterminesResponseIsFalse :
      baselineAutomaticallyDeterminesResponse ≡ false

    differentResponseIdentifiesCompleteMechanism : Bool
    differentResponseIdentifiesCompleteMechanismIsFalse :
      differentResponseIdentifiesCompleteMechanism ≡ false

canonicalContrastiveInterventionBoundary : ContrastiveInterventionBoundary
canonicalContrastiveInterventionBoundary =
  contrastiveInterventionBoundary
    true refl
    true refl
    false refl
    false refl
