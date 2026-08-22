module DASHI.Biology.NeuralResidualDependencyBridgeExact where

------------------------------------------------------------------------
-- NEURAL RESIDUAL DEPENDENCY / REACH-PRESERVING DECOUPLING BRIDGE
--
-- This module instantiates the generic ResidualObserverDependencyExact seam
-- with already-existing DASHI neural carriers.  It does not propose a new
-- neuroscience model.  The finite theorems only connect three distinctions
-- that the repository already keeps separate:
--
--   coarse regional measurement,
--   microscopic/Laplacian variation,
--   state-dependent effective connectivity.
--
-- The main structural theorem is a non-descent result: one coarse fMRI-like
-- observation cannot reconstruct the effective dependency code on the
-- displayed collision.  The second theorem shows why raw coupling minimisation
-- is too weak: the numerically least-coupled admissible transition may close a
-- required association-to-planning route.  The corrected choice minimizes
-- coupling only among transitions whose post-state preserves that capability.
--
-- Sources / calibration:
--
-- R. Matthew Hutchison et al.,
-- "Dynamic functional connectivity: Promise, issues, and interpretations",
-- NeuroImage 80 (2013), DOI 10.1016/j.neuroimage.2013.05.079.
--
-- Gustavo Deco, Viktor K. Jirsa, Peter A. Robinson, Michael Breakspear,
-- Karl Friston,
-- "The Dynamic Brain: From Spiking Neurons to Neural Masses and Cortical
-- Fields", PLoS Computational Biology 4(8), 2008,
-- DOI 10.1371/journal.pcbi.0040100.
--
-- George A. Mashour, Pieter R. Roelfsema, Jean-Pierre Changeux,
-- Stanislas Dehaene,
-- "Conscious Processing and the Global Neuronal Workspace Hypothesis",
-- Neuron 105(5), 2020, DOI 10.1016/j.neuron.2020.01.026.
--
-- Fan R. K. Chung, "Spectral Graph Theory", CBMS 92, AMS 1997,
-- DOI 10.1090/cbms/092.
--
-- Nikhil Bansal and Haotian Jiang,
-- "Decoupling via Affine Spectral-Independence: Beck-Fiala and Komlos Bounds
-- Beyond Banaszczyk", STOC 2026; arXiv:2508.03961,
-- DOI 10.48550/arXiv.2508.03961.
--
-- Claim boundary: the Nat-valued Laplacian variation below is not a covariance
-- operator or affine spectral-independence constant, effective reachability is
-- not identified with consciousness, and this finite bridge is not a clinical
-- or biological sufficiency theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.ResidualObserverDependencyExact as Residual
import DASHI.Biology.NeuralRepresentationLaplacianExact as Neural
import DASHI.Biology.DynamicEffectiveTopology as Dynamic

------------------------------------------------------------------------
-- Joint fine state: microscopic activation plus state-dependent effective
-- topology.  The coarse measurement intentionally observes activation only.
------------------------------------------------------------------------

record BrainState : Set where
  constructor brainState
  field
    activation : Neural.PopulationActivation
    electrochemicalState : Dynamic.ElectrochemicalState

open BrainState public

coarseBrainObservation :
  Observer.Observer BrainState Neural.CoarseRegionalObservation
coarseBrainObservation state =
  Neural.fmriLikeObservation (activation state)

data DependencyProbe : Set where
  inspectEffectiveDependency : DependencyProbe

data EffectiveDependencyCode : Set where
  planningRouteClosed planningRouteOpen : EffectiveDependencyCode

planningDependencyCode :
  BrainState → DependencyProbe → EffectiveDependencyCode
planningDependencyCode (brainState activation Dynamic.inhibitedState) _ =
  planningRouteClosed
planningDependencyCode (brainState activation Dynamic.permissiveState) _ =
  planningRouteClosed
planningDependencyCode (brainState activation Dynamic.recurrentState) _ =
  planningRouteOpen

neuralResidualDependency :
  Residual.ResidualDependencyObserver
    BrainState DependencyProbe Dynamic.Node EffectiveDependencyCode
neuralResidualDependency = record
  { Influences = λ state probe source target →
      Dynamic.Reachable (electrochemicalState state) source target
  ; dependencyCode = planningDependencyCode
  }

recurrentCollisionState : BrainState
recurrentCollisionState =
  brainState Neural.microActivationA Dynamic.recurrentState

inhibitedCollisionState : BrainState
inhibitedCollisionState =
  brainState Neural.microActivationB Dynamic.inhibitedState

collisionHasSameCoarseMeasurement :
  coarseBrainObservation recurrentCollisionState
  ≡ coarseBrainObservation inhibitedCollisionState
collisionHasSameCoarseMeasurement =
  Neural.fmriProjectionCollision

collisionHasDifferentDependencyCode :
  planningDependencyCode recurrentCollisionState inspectEffectiveDependency
  ≡ planningDependencyCode inhibitedCollisionState inspectEffectiveDependency
  → ⊥
collisionHasDifferentDependencyCode ()

hiddenEffectiveDependency :
  Residual.HiddenResidualDependency
    neuralResidualDependency
    coarseBrainObservation
    inspectEffectiveDependency
hiddenEffectiveDependency =
  Residual.hiddenResidualDependency
    recurrentCollisionState
    inhibitedCollisionState
    collisionHasSameCoarseMeasurement
    collisionHasDifferentDependencyCode

neuralDependencyStrictlyRefinesCoarseMeasurement :
  Observer.StrictRefinement
    coarseBrainObservation
    (Residual.refinedObservationAt
      neuralResidualDependency
      coarseBrainObservation
      inspectEffectiveDependency)
neuralDependencyStrictlyRefinesCoarseMeasurement =
  Residual.hiddenResidualDependencyGivesStrictRefinement
    hiddenEffectiveDependency

coarseMeasurementCannotReconstructEffectiveDependency :
  Residual.DependencyCodeDescendsAt
    neuralResidualDependency
    coarseBrainObservation
    inspectEffectiveDependency
  → ⊥
coarseMeasurementCannotReconstructEffectiveDependency =
  Residual.hiddenResidualDependencyBlocksDescent
    hiddenEffectiveDependency

------------------------------------------------------------------------
-- Control example: raw decoupling versus required reach.
------------------------------------------------------------------------

data NeuralControlAction : Set where
  retainRecurrentRoute closeEffectiveRoute : NeuralControlAction

initialControlState : BrainState
initialControlState =
  brainState
    (Neural.populationActivation 0 2 1)
    Dynamic.recurrentState

balancedRecurrentState : BrainState
balancedRecurrentState =
  brainState
    (Neural.populationActivation 2 2 2)
    Dynamic.recurrentState

balancedInhibitedState : BrainState
balancedInhibitedState =
  brainState
    (Neural.populationActivation 2 2 2)
    Dynamic.inhibitedState

data NeuralControlPrecondition : BrainState → NeuralControlAction → Set where
  retainFromInitial :
    NeuralControlPrecondition initialControlState retainRecurrentRoute
  closeFromInitial :
    NeuralControlPrecondition initialControlState closeEffectiveRoute

data NeuralControlPostcondition :
    BrainState → NeuralControlAction → BrainState → Set where
  retainedAndBalanced :
    NeuralControlPostcondition
      initialControlState retainRecurrentRoute balancedRecurrentState
  closedAndBalanced :
    NeuralControlPostcondition
      initialControlState closeEffectiveRoute balancedInhibitedState

neuralControlSystem :
  Dependency.DependentActionSystem BrainState NeuralControlAction
neuralControlSystem = record
  { Precondition = NeuralControlPrecondition
  ; Postcondition = NeuralControlPostcondition
  ; actionLabel = λ
      { retainRecurrentRoute → "retain recurrent effective route"
      ; closeEffectiveRoute → "close effective route"
      }
  }

retainIsAdmissible :
  Dependency.AdmissibleAction
    neuralControlSystem initialControlState retainRecurrentRoute
retainIsAdmissible = record
  { precondition = retainFromInitial
  ; after = balancedRecurrentState
  ; postcondition = retainedAndBalanced
  ; dependencyReceipt =
      "finite calibration transition preserving recurrent effective topology"
  }

closeIsAdmissible :
  Dependency.AdmissibleAction
    neuralControlSystem initialControlState closeEffectiveRoute
closeIsAdmissible = record
  { precondition = closeFromInitial
  ; after = balancedInhibitedState
  ; postcondition = closedAndBalanced
  ; dependencyReceipt =
      "finite calibration transition that suppresses the effective route"
  }

------------------------------------------------------------------------
-- A deliberately crude coupling count makes the failure mode visible:
-- disconnecting everything scores lower than retaining a required route.
------------------------------------------------------------------------

candidateHarmfulCoupling :
  Residual.CouplingScore BrainState NeuralControlAction
candidateHarmfulCoupling state retainRecurrentRoute = 1
candidateHarmfulCoupling state closeEffectiveRoute = 0

closingIsNaivelyLeastCoupled :
  Residual.LeastCoupledAdmissibleChoice
    neuralControlSystem candidateHarmfulCoupling initialControlState
closingIsNaivelyLeastCoupled = record
  { chosenAction = closeEffectiveRoute
  ; chosenAdmissible = closeIsAdmissible
  ; leastAmongAdmissible = λ
      { retainRecurrentRoute alternativeAdmissible → z≤n
      ; closeEffectiveRoute alternativeAdmissible → z≤n
      }
  }

RequiredPlanningRoute : Residual.StateCapability BrainState
RequiredPlanningRoute state =
  Dynamic.EffectiveEdge
    (electrochemicalState state)
    Dynamic.associationNode
    Dynamic.planningNode

balancedRecurrentPreservesPlanningRoute :
  RequiredPlanningRoute balancedRecurrentState
balancedRecurrentPreservesPlanningRoute =
  Dynamic.recurrentAssociationPlanning

balancedInhibitedCannotPreservePlanningRoute :
  RequiredPlanningRoute balancedInhibitedState → ⊥
balancedInhibitedCannotPreservePlanningRoute =
  Dynamic.inhibitedAssociationPlanningImpossible

retainIsLeastCoupledAmongReachPreserving :
  Residual.LeastCoupledCapabilityPreservingChoice
    neuralControlSystem
    candidateHarmfulCoupling
    RequiredPlanningRoute
    initialControlState
retainIsLeastCoupledAmongReachPreserving = record
  { chosenCapabilityAction = retainRecurrentRoute
  ; chosenCapabilityAdmissible = retainIsAdmissible
  ; chosenPreservesCapability = balancedRecurrentPreservesPlanningRoute
  ; leastAmongCapabilityPreserving = λ
      { retainRecurrentRoute alternativeAdmissible capability → ≤-refl
      ; closeEffectiveRoute alternativeAdmissible capability →
          ⊥-elim (balancedInhibitedCannotPreservePlanningRoute capability)
      }
  }

------------------------------------------------------------------------
-- Existing Laplacian variation supplies a real residual-state statistic.
-- Both displayed controls reduce that statistic to zero, so variation alone
-- cannot decide whether required effective reach was preserved.
------------------------------------------------------------------------

residualLaplacianVariation : Residual.ResidualStateScore BrainState
residualLaplacianVariation state =
  Neural.laplacianVariation (activation state)

initialVariationIsThree :
  residualLaplacianVariation initialControlState ≡ 3
initialVariationIsThree = refl

balancedRecurrentVariationIsZero :
  residualLaplacianVariation balancedRecurrentState ≡ 0
balancedRecurrentVariationIsZero = refl

balancedInhibitedVariationIsZero :
  residualLaplacianVariation balancedInhibitedState ≡ 0
balancedInhibitedVariationIsZero = refl

retainStrictlyReducesVariation :
  Residual.StrictlyDecouples
    residualLaplacianVariation retainIsAdmissible
retainStrictlyReducesVariation = s≤s z≤n

closeStrictlyReducesVariation :
  Residual.StrictlyDecouples
    residualLaplacianVariation closeIsAdmissible
closeStrictlyReducesVariation = s≤s z≤n

retainReachPreservingDecoupling :
  Residual.CapabilityPreservingDecoupling
    residualLaplacianVariation
    RequiredPlanningRoute
    retainIsAdmissible
retainReachPreservingDecoupling =
  Residual.capabilityPreservingDecoupling
    balancedRecurrentPreservesPlanningRoute
    z≤n

------------------------------------------------------------------------
-- Exact finite boundary.
------------------------------------------------------------------------

record NeuralResidualDependencyBoundary : Set where
  constructor neuralResidualDependencyBoundary
  field
    coarseMeasurementDeterminesEffectiveDependency : Bool
    coarseMeasurementDeterminesEffectiveDependencyIsFalse :
      coarseMeasurementDeterminesEffectiveDependency ≡ false

    lowerCouplingAutomaticallyPreservesRequiredReach : Bool
    lowerCouplingAutomaticallyPreservesRequiredReachIsFalse :
      lowerCouplingAutomaticallyPreservesRequiredReach ≡ false

    laplacianReductionAloneCertifiesRequiredReach : Bool
    laplacianReductionAloneCertifiesRequiredReachIsFalse :
      laplacianReductionAloneCertifiesRequiredReach ≡ false

    capabilityConstrainedDecouplingConstructed : Bool
    capabilityConstrainedDecouplingConstructedIsTrue :
      capabilityConstrainedDecouplingConstructed ≡ true

    affineSpectralIndependencePromoted : Bool
    affineSpectralIndependencePromotedIsFalse :
      affineSpectralIndependencePromoted ≡ false

canonicalNeuralResidualDependencyBoundary : NeuralResidualDependencyBoundary
canonicalNeuralResidualDependencyBoundary =
  neuralResidualDependencyBoundary
    false refl
    false refl
    false refl
    true refl
    false refl
