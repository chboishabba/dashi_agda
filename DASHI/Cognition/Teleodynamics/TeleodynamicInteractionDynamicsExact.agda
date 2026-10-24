module DASHI.Cognition.Teleodynamics.TeleodynamicInteractionDynamicsExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.DynamicMultiQueryMultiResolutionExact as Dynamic
import DASHI.Cognition.Teleodynamics.LLMGeometricPriorBridgeExact as LLM
import DASHI.Cognition.TeleodynamicsPrincipiaTwoExact as T

------------------------------------------------------------------------
-- TELEODYNAMIC REPEATED-INTERACTION DYNAMICS
--
-- Repeated teacher/student or system/system interactions are routed through the
-- existing dynamic multi-query abstraction.  Static representation fit does not
-- imply that compression/selection commutes with future transitions.
------------------------------------------------------------------------

record TeleodynamicInteractionDynamics : Set where
  constructor teleodynamicInteractionDynamics
  field
    fineStateLabel : String
    interactionActionLabel : String
    fineTransitionLabel : String
    compressedTransitionLabel : String
    localResidualTransitionLabel : String
    queryFamilyLabel : String
    commutationObligationLabel : String
    futureTraceLabel : String

record InteractionDynamicsBoundary : Set where
  constructor interactionDynamicsBoundary
  field
    dynamicMultiQueryOwnerReused : Bool
    oneStepFitImpliesArbitraryTraceSafety : Bool
    staticArchitectureSimilarityImpliesTransitionCommutation : Bool
    interactionDynamicsEstablishNonlocalTransmission : Bool
    futureTraceMustBeCheckedSeparately : Bool

open InteractionDynamicsBoundary public

canonicalInteractionDynamicsBoundary : InteractionDynamicsBoundary
canonicalInteractionDynamicsBoundary =
  interactionDynamicsBoundary true false false false true

canonicalInteractionDynamics : TeleodynamicInteractionDynamics
canonicalInteractionDynamics =
  teleodynamicInteractionDynamics
    "fine learner/system state"
    "declared interaction/query action"
    "fine transition"
    "retained global transition"
    "local residual transition"
    "declared consumer query family"
    "coarse/local abstraction commutes with each declared transition"
    "arbitrary finite interaction trace"
