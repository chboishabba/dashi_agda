module DASHI.Cognition.PredictiveAgencyBridge where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Prediction is a general state-update surface
------------------------------------------------------------------------

record Predictor (State Symbol : Set) : Set₁ where
  field
    next    : State → Symbol
    advance : State → Symbol → State

-- A predictor may be realised in linguistic, transcriptional,
-- physiological, anatomical, or ordinary spatial state space.  The carrier
-- is deliberately abstract: next-symbol prediction is not restricted to text.
record PredictionRealisation
  (State Symbol Observation : Set)
  (P : Predictor State Symbol) : Set₁ where
  field
    observe : State → Observation
    decode  : Observation → Symbol
    predictionObserved : (s : State) →
      decode (observe s) ≡ Predictor.next P s

------------------------------------------------------------------------
-- Operational agency requires counterfactual correction, not prediction alone
------------------------------------------------------------------------

record GoalCorrection (State Barrier : Set) : Set₁ where
  field
    Goal       : State → Set
    disturb    : State → Barrier → State
    correct    : State → Barrier → State

    -- William James's "same end by different means" criterion, stated as a
    -- counterfactual intervention law: after any admitted barrier, correction
    -- returns the system to the same goal predicate.
    recovers :
      (s : State) → Goal s → (b : Barrier) →
      Goal (correct (disturb s b) b)

record PredictiveAgency (State Symbol Barrier : Set) : Set₁ where
  field
    predictor  : Predictor State Symbol
    correction : GoalCorrection State Barrier

-- Forgetting the correction protocol leaves an ordinary predictor.
-- This direction is exact.  No converse is supplied: next-symbol prediction
-- alone neither proves nor disproves operational agency.
forgetCorrection :
  {State Symbol Barrier : Set} →
  PredictiveAgency State Symbol Barrier →
  Predictor State Symbol
forgetCorrection A = PredictiveAgency.predictor A

record AgencyExtension
  {State Symbol Barrier : Set}
  (P : Predictor State Symbol) : Set₁ where
  field
    correction : GoalCorrection State Barrier

extendPredictor :
  {State Symbol Barrier : Set} →
  (P : Predictor State Symbol) →
  AgencyExtension {Barrier = Barrier} P →
  PredictiveAgency State Symbol Barrier
PredictiveAgency.predictor
  (extendPredictor P extension) = P
PredictiveAgency.correction
  (extendPredictor P extension) = AgencyExtension.correction extension

------------------------------------------------------------------------
-- Observer-relative interaction protocols
------------------------------------------------------------------------

record InteractionProtocol (System Tool Outcome : Set) : Set₁ where
  field
    applyTool : Tool → System → System
    readOut   : System → Outcome

record ProtocolClaim
  {System Tool Outcome : Set}
  (protocol : InteractionProtocol System Tool Outcome) : Set₁ where
  field
    Capacity : Outcome → Set
    witness  : (tool : Tool) (system : System) →
      Capacity
        (InteractionProtocol.readOut protocol
          (InteractionProtocol.applyTool protocol tool system))

------------------------------------------------------------------------
-- Multiscale agency as a commuting correction square
------------------------------------------------------------------------

record ScaleMap (Fine Coarse : Set) : Set₁ where
  field
    coarseGrain : Fine → Coarse

record MultiscaleCorrection
  {Fine Coarse FineBarrier CoarseBarrier : Set}
  (fine   : GoalCorrection Fine FineBarrier)
  (coarse : GoalCorrection Coarse CoarseBarrier)
  (scale  : ScaleMap Fine Coarse) : Set₁ where
  field
    liftBarrier : FineBarrier → CoarseBarrier

    goalPreserved : (s : Fine) →
      GoalCorrection.Goal fine s →
      GoalCorrection.Goal coarse (ScaleMap.coarseGrain scale s)

    correctionCommutes : (s : Fine) (b : FineBarrier) →
      ScaleMap.coarseGrain scale
        (GoalCorrection.correct fine
          (GoalCorrection.disturb fine s b) b)
      ≡
      GoalCorrection.correct coarse
        (GoalCorrection.disturb coarse
          (ScaleMap.coarseGrain scale s)
          (liftBarrier b))
        (liftBarrier b)

------------------------------------------------------------------------
-- Claim boundary
------------------------------------------------------------------------

-- These statuses prevent operational goal-directedness from silently promoting
-- itself into phenomenology, panpsychism, or retrocausal physics.
data PredictiveAgencyStatus : Set where
  operationalAgencyOnly      : PredictiveAgencyStatus
  consciousnessNotDerived    : PredictiveAgencyStatus
  panpsychismNotDerived      : PredictiveAgencyStatus
  retrocausalityNotDerived   : PredictiveAgencyStatus
