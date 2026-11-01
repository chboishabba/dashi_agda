module DASHI.Interop.SLRBoundedResearchIterationControlExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRSelectedRouteExecutionNextObservationExact as Execution
import DASHI.Interop.SLRSpacyObservationWorldCompilerParityExact as Observation

------------------------------------------------------------------------
-- BOUNDED RESEARCH ITERATION CONTROL
--
-- Runtime owner:
--   tools/slr-discourse-reconstruct/run_world_research_iteration_loop.sh
--
-- The controller has no semantic authority. It only decides whether an
-- already-produced binary SLRO stream is admitted as the next iteration's
-- parser input. It advances iff the next observation stream is non-empty,
-- not byte-identical to the current observation, and the explicit iteration
-- budget has not been exhausted.
------------------------------------------------------------------------

data IterationDecision : Set where
  continueWithNextObservation : IterationDecision
  stopNoNextObservation : IterationDecision
  stopRepeatedObservation : IterationDecision
  stopMaximumIterations : IterationDecision

record IterationControlParity : Set where
  constructor iterationControlParity
  field
    nextInputUsesSLRO : Bool
    acquiredSourceTransitionUsesSLRX : Bool
    explicitPositiveIterationBoundRequired : Bool
    nonEmptyNextObservationRequired : Bool
    byteIdenticalObservationMayAdvance : Bool
    deferredOnlyRoundStops : Bool
    maximumIterationsStops : Bool
    repeatedObservationStops : Bool
    controllerParsesJson : Bool
    controllerUsesRegexSemantics : Bool
    controllerCreatesClaimTruth : Bool
    controllerCreatesEvidencePayment : Bool
    controllerCreatesSemanticAuthority : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open IterationControlParity public

canonicalIterationControlParity : IterationControlParity
canonicalIterationControlParity =
  iterationControlParity
    true true true true false true true true
    false false false false false true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data EmptyNextObservationAdvances : Set where
data RepeatedObservationAdvances : Set where
data IterationControllerCreatesClaimTruth : Set where
data IterationControllerCreatesEvidencePayment : Set where
data IterationControllerCreatesSemanticAuthority : Set where
data IterationControllerUsesJson : Set where
data IterationControllerUsesRegexSemantics : Set where

emptyNextObservationCannotAdvance : EmptyNextObservationAdvances → ⊥
emptyNextObservationCannotAdvance ()

repeatedObservationCannotAdvance : RepeatedObservationAdvances → ⊥
repeatedObservationCannotAdvance ()

iterationControllerDoesNotCreateClaimTruth : IterationControllerCreatesClaimTruth → ⊥
iterationControllerDoesNotCreateClaimTruth ()

iterationControllerDoesNotCreateEvidencePayment : IterationControllerCreatesEvidencePayment → ⊥
iterationControllerDoesNotCreateEvidencePayment ()

iterationControllerDoesNotCreateSemanticAuthority : IterationControllerCreatesSemanticAuthority → ⊥
iterationControllerDoesNotCreateSemanticAuthority ()

iterationControllerJsonForbidden : IterationControllerUsesJson → ⊥
iterationControllerJsonForbidden ()

iterationControllerRegexSemanticsForbidden : IterationControllerUsesRegexSemantics → ⊥
iterationControllerRegexSemanticsForbidden ()

routeExecutionAnchor : Execution.SelectedRouteExecutionParity
routeExecutionAnchor = Execution.canonicalSelectedRouteExecutionParity

observationWireVersionAnchor : Nat
observationWireVersionAnchor = Observation.observationWireVersion
