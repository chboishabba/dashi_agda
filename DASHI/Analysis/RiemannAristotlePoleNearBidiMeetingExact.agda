module DASHI.Analysis.RiemannAristotlePoleNearBidiMeetingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact as Eval
import DASHI.Analysis.RiemannAristotlePoleNearPhaseStatisticExact as Phase
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as EFBridge

------------------------------------------------------------------------
-- BIDI MEETING POINT
--
-- The direct and explicit-formula routes are allowed to differ internally, but
-- neither changes the RH consumer.  Both must end in the exact same kind of
-- SignedFiniteNearEvaluationSurface before they can generate B_near.
------------------------------------------------------------------------

data PoleNearAttackRoute : Set where
  directPhaseRoute
  explicitFormulaWindowRoute
  : PoleNearAttackRoute

record PoleNearRouteEvaluation (route : PoleNearAttackRoute) : Set₁ where
  constructor pole-near-route-evaluation
  field
    evaluation : Eval.SignedFiniteNearEvaluationSurface
    routeReference : String

open PoleNearRouteEvaluation public

record DirectPhaseToEvaluation : Set₁ where
  constructor direct-phase-to-evaluation
  field
    phaseStatistic : Phase.PoleNearPhaseStatistic
    phaseControl : Phase.PhaseStatisticControlsFiniteNear phaseStatistic
    output : PoleNearRouteEvaluation directPhaseRoute

open DirectPhaseToEvaluation public

record ExplicitFormulaToEvaluation : Set₁ where
  constructor explicit-formula-to-evaluation
  field
    OutputWitness : Set
    outputWitness : OutputWitness
    output : PoleNearRouteEvaluation explicitFormulaWindowRoute
    outputIsLiteralPoleNearEvaluation : Set

open ExplicitFormulaToEvaluation public

record PoleNearBidiMeeting
    (direct : DirectPhaseToEvaluation)
    (explicit : ExplicitFormulaToEvaluation) : Set₁ where
  constructor pole-near-bidi-meeting
  field
    SameEvaluationCarrier :
      Eval.SignedFiniteNearEvaluationSurface →
      Eval.SignedFiniteNearEvaluationSurface → Set

    routesMeetAtSameConsumerSurface :
      SameEvaluationCarrier
        (evaluation (DirectPhaseToEvaluation.output direct))
        (evaluation (ExplicitFormulaToEvaluation.output explicit))

    meetingReference : String

open PoleNearBidiMeeting public

record PoleNearBidiMeetingBoundary : Set where
  constructor pole-near-bidi-meeting-boundary
  field
    directAndExplicitRoutesMayUseDifferentInternalProofObjects : Bool
    directAndExplicitRoutesMayUseDifferentInternalProofObjectsIsTrue :
      directAndExplicitRoutesMayUseDifferentInternalProofObjects ≡ true

    routesMayChangeFinalRHConsumer : Bool
    routesMayChangeFinalRHConsumerIsFalse : routesMayChangeFinalRHConsumer ≡ false

    bothRoutesMustProduceSignedEvaluationReceipt : Bool
    bothRoutesMustProduceSignedEvaluationReceiptIsTrue :
      bothRoutesMustProduceSignedEvaluationReceipt ≡ true

    bidiMeetingClosedAnalytically : Bool
    bidiMeetingClosedAnalyticallyIsFalse : bidiMeetingClosedAnalytically ≡ false

    boundedReading : String

canonicalPoleNearBidiMeetingBoundary : PoleNearBidiMeetingBoundary
canonicalPoleNearBidiMeetingBoundary =
  pole-near-bidi-meeting-boundary
    true refl
    false refl
    true refl
    false refl
    "The direct phase-statistic route and the explicit-formula target-window route are pursued simultaneously, but both are only successful for RH when they inhabit the same consumer-facing signed finite-near evaluation surface. Neither route is allowed to redefine H_off^pole or weaken the downstream complement window."
