module DASHI.Biology.NeuralResidualFutureLanguageBridgeExact where

------------------------------------------------------------------------
-- NEURAL RESIDUAL DEPENDENCY -> FUTURE-LANGUAGE CAPABILITY
--
-- This bridge turns the planning-reach capability used by
-- NeuralResidualDependencyBridgeExact into the repository's existing exact
-- future-observation language.  A one-step consumer-visible action
-- `readPlanning` is admissible exactly when the current fine state carries the
-- required association-to-planning effective-edge witness.  Thus preserving
-- the capability is no longer only a static edge predicate: it preserves an
-- actual future action/observation trace.
--
-- Sources / calibration:
--
-- George A. Mashour, Pieter R. Roelfsema, Jean-Pierre Changeux,
-- Stanislas Dehaene,
-- "Conscious Processing and the Global Neuronal Workspace Hypothesis",
-- Neuron 105(5), 2020, DOI 10.1016/j.neuron.2020.01.026.
--
-- R. Matthew Hutchison et al.,
-- "Dynamic functional connectivity: Promise, issues, and interpretations",
-- NeuroImage 80 (2013), DOI 10.1016/j.neuroimage.2013.05.079.
--
-- Nikhil Bansal and Haotian Jiang,
-- "Decoupling via Affine Spectral-Independence: Beck-Fiala and Komlos Bounds
-- Beyond Banaszczyk", STOC 2026, DOI 10.1145/3798129.3800762;
-- arXiv:2508.03961, DOI 10.48550/arXiv.2508.03961.
--
-- The Bansal--Jiang source calibrates only the control principle that useful
-- decoupling preserves required constraints while controlling interactions.
-- This module does not claim that neural access implements their SDP/Brownian
-- algorithm, or that this finite trace is sufficient for consciousness.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.ResidualObserverDependencyExact as Residual
import DASHI.Biology.NeuralResidualDependencyBridgeExact as Neural
import DASHI.Biology.DynamicEffectiveTopology as Dynamic

data PlanningReadAction : Set where
  readPlanning : PlanningReadAction

data PlanningReadPostcondition :
    Neural.BrainState → PlanningReadAction → Neural.BrainState → Set where
  readPlanningPreservesState :
    ∀ {state} →
    PlanningReadPostcondition state readPlanning state

planningReadSystem :
  Dependency.DependentActionSystem Neural.BrainState PlanningReadAction
planningReadSystem = record
  { Precondition = λ state action → Neural.RequiredPlanningRoute state
  ; Postcondition = PlanningReadPostcondition
  ; actionLabel = λ { readPlanning → "read planning-accessible content" }
  }

planningAvailableObservation : Neural.BrainState → Bool
planningAvailableObservation
  (Neural.brainState activation Dynamic.inhibitedState) = false
planningAvailableObservation
  (Neural.brainState activation Dynamic.permissiveState) = false
planningAvailableObservation
  (Neural.brainState activation Dynamic.recurrentState) = true

recurrentPlanningReadAdmissible :
  Dependency.AdmissibleAction
    planningReadSystem
    Neural.balancedRecurrentState
    readPlanning
recurrentPlanningReadAdmissible = record
  { precondition = Neural.balancedRecurrentPreservesPlanningRoute
  ; after = Neural.balancedRecurrentState
  ; postcondition = readPlanningPreservesState
  ; dependencyReceipt =
      "planning read is admitted by the existing recurrent effective-edge witness"
  }

recurrentPlanningFutureObservation :
  Future.FutureObservation
    planningReadSystem
    planningAvailableObservation
    Neural.balancedRecurrentState
    (readPlanning ∷ [])
    true
recurrentPlanningFutureObservation =
  Future.futureObservation
    Neural.balancedRecurrentState
    (Reachability.executesCons recurrentPlanningReadAdmissible
      Reachability.executesNil)
    refl

inhibitedPlanningReadImpossible :
  Dependency.AdmissibleAction
    planningReadSystem
    Neural.balancedInhibitedState
    readPlanning → ⊥
inhibitedPlanningReadImpossible admissible =
  Neural.balancedInhibitedCannotPreservePlanningRoute
    (Dependency.precondition admissible)

inhibitedPlanningFutureObservationImpossible :
  Future.FutureObservation
    planningReadSystem
    planningAvailableObservation
    Neural.balancedInhibitedState
    (readPlanning ∷ [])
    true → ⊥
inhibitedPlanningFutureObservationImpossible
  (Future.futureObservation after
    (Reachability.executesCons admissible rest)
    observationEquality) =
  inhibitedPlanningReadImpossible admissible

RequiredPlanningFutureLanguage :
  Residual.StateCapability Neural.BrainState
RequiredPlanningFutureLanguage state =
  Future.FutureObservation
    planningReadSystem
    planningAvailableObservation
    state
    (readPlanning ∷ [])
    true

retainPreservesPlanningFutureLanguage :
  RequiredPlanningFutureLanguage Neural.balancedRecurrentState
retainPreservesPlanningFutureLanguage = recurrentPlanningFutureObservation

closeAdmissibleCannotPreservePlanningFutureLanguage :
  (admissible :
    Dependency.AdmissibleAction
      Neural.neuralControlSystem
      Neural.initialControlState
      Neural.closeEffectiveRoute) →
  RequiredPlanningFutureLanguage (Dependency.after admissible) → ⊥
closeAdmissibleCannotPreservePlanningFutureLanguage admissible capability
  with Dependency.postcondition admissible
... | Neural.closedAndBalanced =
  inhibitedPlanningFutureObservationImpossible capability

retainIsLeastCoupledAmongFutureLanguagePreserving :
  Residual.LeastCoupledCapabilityPreservingChoice
    Neural.neuralControlSystem
    Neural.candidateHarmfulCoupling
    RequiredPlanningFutureLanguage
    Neural.initialControlState
retainIsLeastCoupledAmongFutureLanguagePreserving = record
  { chosenCapabilityAction = Neural.retainRecurrentRoute
  ; chosenCapabilityAdmissible = Neural.retainIsAdmissible
  ; chosenPreservesCapability = retainPreservesPlanningFutureLanguage
  ; leastAmongCapabilityPreserving = λ
      { Neural.retainRecurrentRoute alternativeAdmissible capability → ≤-refl
      ; Neural.closeEffectiveRoute alternativeAdmissible capability →
          ⊥-elim
            (closeAdmissibleCannotPreservePlanningFutureLanguage
              alternativeAdmissible capability)
      }
  }

postStatesHaveEqualLaplacianResidual :
  Neural.residualLaplacianVariation Neural.balancedRecurrentState
  ≡ Neural.residualLaplacianVariation Neural.balancedInhibitedState
postStatesHaveEqualLaplacianResidual = refl

equalLaplacianResidualDoesNotForceEqualFuturePlanningLanguage :
  RequiredPlanningFutureLanguage Neural.balancedRecurrentState
  ×
  (RequiredPlanningFutureLanguage Neural.balancedInhibitedState → ⊥)
equalLaplacianResidualDoesNotForceEqualFuturePlanningLanguage =
  recurrentPlanningFutureObservation
  , inhibitedPlanningFutureObservationImpossible

------------------------------------------------------------------------
-- Exact quotient-safety failure for the scalar residual observer.
--
-- The two displayed states collide under residualLaplacianVariation, but the
-- one-step future planning language separates them.  Therefore that scalar
-- projection cannot satisfy FutureLanguageSafeProjection for this consumer.
------------------------------------------------------------------------

laplacianResidualNotFutureLanguageSafe :
  Future.FutureLanguageSafeProjection
    planningReadSystem
    planningAvailableObservation
    Neural.residualLaplacianVariation → ⊥
laplacianResidualNotFutureLanguageSafe safe =
  inhibitedPlanningFutureObservationImpossible
    (Future.forward
      (Future.sameFutureLanguage equivalent
        (readPlanning ∷ []) true)
      recurrentPlanningFutureObservation)
  where
    equivalent :
      Future.FutureObservationEquivalent
        planningReadSystem
        planningAvailableObservation
        Neural.balancedRecurrentState
        Neural.balancedInhibitedState
    equivalent =
      Future.kernelContainedInFutureEquivalence safe
        postStatesHaveEqualLaplacianResidual

record NeuralResidualFutureLanguageBoundary : Set where
  constructor neuralResidualFutureLanguageBoundary
  field
    equalScalarResidualForcesEqualFutureLanguage : Bool
    equalScalarResidualForcesEqualFutureLanguageIsFalse :
      equalScalarResidualForcesEqualFutureLanguage ≡ false
    scalarResidualIsFutureLanguageSafe : Bool
    scalarResidualIsFutureLanguageSafeIsFalse :
      scalarResidualIsFutureLanguageSafe ≡ false
    futureLanguageCapabilityConstrainsDecoupling : Bool
    futureLanguageCapabilityConstrainsDecouplingIsTrue :
      futureLanguageCapabilityConstrainsDecoupling ≡ true
    planningTraceSufficientForConsciousness : Bool
    planningTraceSufficientForConsciousnessIsFalse :
      planningTraceSufficientForConsciousness ≡ false

canonicalNeuralResidualFutureLanguageBoundary :
  NeuralResidualFutureLanguageBoundary
canonicalNeuralResidualFutureLanguageBoundary =
  neuralResidualFutureLanguageBoundary
    false refl
    false refl
    true refl
    false refl
