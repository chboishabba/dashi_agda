module DASHI.Cognition.PredictiveAgencyBridgeTests where

open import DASHI.Core.Prelude
open import DASHI.Cognition.PredictiveAgencyBridge

------------------------------------------------------------------------
-- A minimal next-symbol predictor
------------------------------------------------------------------------

boolPredictor : Predictor Bool Bool
Predictor.next boolPredictor state = state
Predictor.advance boolPredictor state symbol = symbol

nextTrue : Predictor.next boolPredictor true ≡ true
nextTrue = refl

advanceChangesState : Predictor.advance boolPredictor false true ≡ true
advanceChangesState = refl

------------------------------------------------------------------------
-- A minimal counterfactual correction witness
------------------------------------------------------------------------

boolCorrection : GoalCorrection Bool Bool
GoalCorrection.Goal boolCorrection state = ⊤
GoalCorrection.disturb boolCorrection state barrier = barrier
GoalCorrection.correct boolCorrection state barrier = true
GoalCorrection.recovers boolCorrection state atGoal barrier = tt

boolAgency : PredictiveAgency Bool Bool Bool
PredictiveAgency.predictor boolAgency = boolPredictor
PredictiveAgency.correction boolAgency = boolCorrection

forgetLaw : forgetCorrection boolAgency ≡ boolPredictor
forgetLaw = refl

boolExtension : AgencyExtension {Barrier = Bool} boolPredictor
AgencyExtension.correction boolExtension = boolCorrection

extensionLaw :
  forgetCorrection (extendPredictor boolPredictor boolExtension) ≡ boolPredictor
extensionLaw = refl

------------------------------------------------------------------------
-- Protocol-relative capacity witness
------------------------------------------------------------------------

boolProtocol : InteractionProtocol Bool Bool Bool
InteractionProtocol.applyTool boolProtocol tool system = tool
InteractionProtocol.readOut boolProtocol system = system

trueCapacity : Bool → Set
trueCapacity true = ⊤
trueCapacity false = ⊤

boolProtocolClaim : ProtocolClaim boolProtocol
ProtocolClaim.Capacity boolProtocolClaim = trueCapacity
ProtocolClaim.witness boolProtocolClaim tool system = tt

------------------------------------------------------------------------
-- Identity multiscale correction square
------------------------------------------------------------------------

identityScale : ScaleMap Bool Bool
ScaleMap.coarseGrain identityScale state = state

identityMultiscale :
  MultiscaleCorrection boolCorrection boolCorrection identityScale
MultiscaleCorrection.liftBarrier identityMultiscale barrier = barrier
MultiscaleCorrection.goalPreserved identityMultiscale state atGoal = tt
MultiscaleCorrection.correctionCommutes identityMultiscale state barrier = refl

operationalBoundary : PredictiveAgencyStatus
operationalBoundary = operationalAgencyOnly

phenomenologyBoundary : PredictiveAgencyStatus
phenomenologyBoundary = consciousnessNotDerived
