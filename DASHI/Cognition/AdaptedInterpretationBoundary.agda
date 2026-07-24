module DASHI.Cognition.AdaptedInterpretationBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Present-adapted action versus retrospective trajectory interpretation.
------------------------------------------------------------------------

record InformationAt (Time Information : Set) : Set₁ where
  field
    available : Time → Information

open InformationAt public

record AdaptedPolicy
    (Time Information Action : Set) : Set₁ where
  field
    choose :
      Time →
      Information →
      Action

open AdaptedPolicy public

record DecisionFrame
    (Time Information Action : Set)
    (policy : AdaptedPolicy Time Information Action) : Set where
  field
    decisionTime : Time
    currentInformation : Information
    selectedAction : Action
    selectedFromCurrentInformation :
      selectedAction ≡ choose policy decisionTime currentInformation

open DecisionFrame public

record ReconstructedMeaningFrame
    (Time Information Action Outcome Meaning : Set) : Set₁ where
  field
    startTime endTime : Time
    priorInformation : Information
    posteriorInformation : Information
    action : Action
    outcome : Outcome
    reconstructedMeaning : Meaning

open ReconstructedMeaningFrame public

data InterpretationStyle : Set where
  itoLikeDecisionReading : InterpretationStyle
  stratonovichLikeTrajectoryReading : InterpretationStyle

record InterpretationCorrection
    (DecisionState TrajectoryState Residual : Set) : Set₁ where
  field
    decisionState : DecisionState
    trajectoryState : TrajectoryState
    correctionResidual : Residual

open InterpretationCorrection public

record AdaptedInterpretationAuthorityBoundary : Set where
  constructor adaptedInterpretationAuthorityBoundary
  field
    noFutureInformationInDecision : Bool
    retrospectiveMeaningMayUseOutcome : Bool
    conversionRequiresResidual : Bool
    literalBrainSDEClaimPromoted : Bool
    literalBrainSDEClaimPromotedIsFalse :
      literalBrainSDEClaimPromoted ≡ false

canonicalAdaptedInterpretationBoundary :
  AdaptedInterpretationAuthorityBoundary
canonicalAdaptedInterpretationBoundary =
  adaptedInterpretationAuthorityBoundary
    true true true false refl
