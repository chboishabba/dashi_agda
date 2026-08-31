module DASHI.Biology.CrossKingdomAnaestheticMechanismFibreRefinementExact where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Biology.CrossKingdomAnaestheticExcitabilityFlowBidiExact as Flow

------------------------------------------------------------------------
-- OPERATIONAL REVERSE-FIBRE REFINEMENT
--
-- This module turns the uncertainty seam into an exact finite theorem.
-- Synthetic mechanism states may agree on a coarse behavioural observation
-- while voltage/current evidence separates them. The construction proves the
-- observer-refinement theorem shape only; it does not claim these synthetic
-- states are empirical anaesthetic targets in plants or animals.
------------------------------------------------------------------------

data MechanismCandidate : Set where
  channelCandidate
  membraneCandidate
  pumpCandidate
  : MechanismCandidate

data BehaviourObservation : Set where
  suppressedBehaviour : BehaviourObservation

data VoltageObservation : Set where
  voltagePatternA
  voltagePatternB
  : VoltageObservation

data CurrentObservation : Set where
  currentPatternA
  currentPatternB
  : CurrentObservation

behaviourObserver :
  Observer.Observer MechanismCandidate BehaviourObservation
behaviourObserver channelCandidate = suppressedBehaviour
behaviourObserver membraneCandidate = suppressedBehaviour
behaviourObserver pumpCandidate = suppressedBehaviour

voltageObserver :
  Observer.Observer MechanismCandidate VoltageObservation
voltageObserver channelCandidate = voltagePatternA
voltageObserver membraneCandidate = voltagePatternB
voltageObserver pumpCandidate = voltagePatternB

currentObserver :
  Observer.Observer MechanismCandidate CurrentObservation
currentObserver channelCandidate = currentPatternA
currentObserver membraneCandidate = currentPatternB
currentObserver pumpCandidate = currentPatternA

channelMembraneSameBehaviour :
  behaviourObserver channelCandidate
  ≡ behaviourObserver membraneCandidate
channelMembraneSameBehaviour = refl

channelMembraneVoltageSeparates :
  voltageObserver channelCandidate
  ≡ voltageObserver membraneCandidate → ⊥
channelMembraneVoltageSeparates ()

behaviourPlusVoltageStrictlyRefinesBehaviour :
  Observer.StrictRefinement
    behaviourObserver
    (Observer.pairObserver behaviourObserver voltageObserver)
behaviourPlusVoltageStrictlyRefinesBehaviour =
  Observer.strictPairRefinement
    behaviourObserver
    voltageObserver
    channelCandidate
    membraneCandidate
    channelMembraneSameBehaviour
    channelMembraneVoltageSeparates

------------------------------------------------------------------------
-- A second measurement can refine the remaining voltage collision.
------------------------------------------------------------------------

membranePumpSameVoltage :
  voltageObserver membraneCandidate ≡ voltageObserver pumpCandidate
membranePumpSameVoltage = refl

membranePumpCurrentSeparates :
  currentObserver membraneCandidate
  ≡ currentObserver pumpCandidate → ⊥
membranePumpCurrentSeparates ()

voltagePlusCurrentStrictlyRefinesVoltage :
  Observer.StrictRefinement
    voltageObserver
    (Observer.pairObserver voltageObserver currentObserver)
voltagePlusCurrentStrictlyRefinesVoltage =
  Observer.strictPairRefinement
    voltageObserver
    currentObserver
    membraneCandidate
    pumpCandidate
    membranePumpSameVoltage
    membranePumpCurrentSeparates

------------------------------------------------------------------------
-- Explicit residual-fibre monotonicity using the generic family theorem.
------------------------------------------------------------------------

behaviourFamily :
  Observer.ObserverFamily MechanismCandidate BehaviourObservation
behaviourFamily = behaviourObserver ∷ []

record CandidateCompatibilityReceipt : Set₁ where
  constructor candidateCompatibilityReceipt
  field
    Candidate : Set
    Measurement : Set
    ErrorBound : Set
    predictsWithinBound : Candidate → Measurement → ErrorBound → Set
    measurement : Measurement
    errorBound : ErrorBound
    calibrationReference : String
    forwardModelReference : String

open CandidateCompatibilityReceipt public

record MechanismFibreRefinementBoundary : Set where
  constructor mechanismFibreRefinementBoundary
  field
    behaviourAloneCanLeaveMultipleMechanisms : Bool
    behaviourAloneCanLeaveMultipleMechanismsIsTrue :
      behaviourAloneCanLeaveMultipleMechanisms ≡ true
    voltageCanStrictlyRefineBehaviourFibre : Bool
    voltageCanStrictlyRefineBehaviourFibreIsTrue :
      voltageCanStrictlyRefineBehaviourFibre ≡ true
    currentCanStrictlyRefineVoltageFibre : Bool
    currentCanStrictlyRefineVoltageFibreIsTrue :
      currentCanStrictlyRefineVoltageFibre ≡ true
    refinementAutomaticallyIdentifiesUniqueTrueMechanism : Bool
    refinementAutomaticallyIdentifiesUniqueTrueMechanismIsFalse :
      refinementAutomaticallyIdentifiesUniqueTrueMechanism ≡ false
    boundedErrorMustRemainExplicit : Bool
    boundedErrorMustRemainExplicitIsTrue :
      boundedErrorMustRemainExplicit ≡ true
    syntheticWitnessIsEmpiricalTargetIdentification : Bool
    syntheticWitnessIsEmpiricalTargetIdentificationIsFalse :
      syntheticWitnessIsEmpiricalTargetIdentification ≡ false

canonicalMechanismFibreRefinementBoundary : MechanismFibreRefinementBoundary
canonicalMechanismFibreRefinementBoundary =
  mechanismFibreRefinementBoundary
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl

------------------------------------------------------------------------
-- Weld to the preceding quantitative owner: the refinement theorem is the
-- operational realization of its bounded-candidate reverse-inference seam.
------------------------------------------------------------------------

record AnaestheticMechanismFibreRefinementWeld : Set₁ where
  constructor anaestheticMechanismFibreRefinementWeld
  field
    uncertaintyReceipt : Flow.ExcitabilityUncertaintyReceipt
    behaviourVoltageRefinement :
      Observer.StrictRefinement
        behaviourObserver
        (Observer.pairObserver behaviourObserver voltageObserver)
    voltageCurrentRefinement :
      Observer.StrictRefinement
        voltageObserver
        (Observer.pairObserver voltageObserver currentObserver)
    compatibilityReceipt : CandidateCompatibilityReceipt

open AnaestheticMechanismFibreRefinementWeld public
