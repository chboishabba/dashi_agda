module DASHI.Physics.Textile.DiscreteTextileFracturePropagationExact where

open import DASHI.Core.Prelude
import Data.Fin as Fin

import DASHI.Physics.Units.MechanicalDimensionExact as Dim
import DASHI.Physics.Textile.TextileMechanicalFibreExact as Mechanics
import DASHI.Physics.Textile.QuasiStaticTextileLoadTransferExact as Load
import DASHI.Physics.Textile.FiniteTextileEquilibriumNetworkExact as Network
import DASHI.Physics.Textile.TextileFailureSlipPredicateExact as Predicate

------------------------------------------------------------------------
-- Discrete fracture propagation on the finite equilibrium network.
--
-- A tensile-threshold witness alone does not create a fracture.  A producer
-- must supply the fracture transition.  Once supplied, this module enforces
-- one-edge damage, preservation of every other edge-integrity coordinate,
-- removal of axial force from the failed edge, and a new equilibrium network.
------------------------------------------------------------------------

data EdgeIntegrity : Set where
  intact : EdgeIntegrity
  broken : EdgeIntegrity

record FiniteDamageState (edgeCount : Nat) : Set where
  constructor finite-damage-state
  field
    integrity : Fin.Fin edgeCount → EdgeIntegrity

open FiniteDamageState public

record FractureMechanicalState
    {Scalar : Set}
    (algebra : Network.OrientedMechanicalAlgebra Scalar)
    (vertexCount edgeCount : Nat) : Set₁ where
  constructor fracture-mechanical-state
  field
    equilibriumNetwork :
      Network.FiniteTextileEquilibriumNetwork algebra vertexCount edgeCount
    damage : FiniteDamageState edgeCount

open FractureMechanicalState public

record DiscreteFractureTransition
    {Scalar : Set}
    (algebra : Network.OrientedMechanicalAlgebra Scalar)
    (vertexCount edgeCount : Nat)
    (before after : FractureMechanicalState algebra vertexCount edgeCount) : Set₁ where
  constructor discrete-fracture-transition
  field
    yarnAtEdge : Fin.Fin edgeCount → Mechanics.YarnConstitutiveState Scalar
    failedEdge : Fin.Fin edgeCount

    thresholdWasExceeded :
      Predicate.TensileThresholdExceeded
        (Network.localAlgebra algebra)
        (yarnAtEdge failedEdge)

    failedEdgeWasIntact :
      integrity (damage before) failedEdge ≡ intact

    failedEdgeIsBrokenAfter :
      integrity (damage after) failedEdge ≡ broken

    allOtherEdgeIntegrityPreserved :
      (edge : Fin.Fin edgeCount) →
      (edge ≡ failedEdge → ⊥) →
      integrity (damage after) edge ≡ integrity (damage before) edge

    sourceTopologyPreserved :
      (edge : Fin.Fin edgeCount) →
      Network.source (equilibriumNetwork after) edge
      ≡ Network.source (equilibriumNetwork before) edge

    targetTopologyPreserved :
      (edge : Fin.Fin edgeCount) →
      Network.target (equilibriumNetwork after) edge
      ≡ Network.target (equilibriumNetwork before) edge

    failedEdgeCarriesZeroAxialForceAfter :
      Dim.magnitude
        (Network.edgeForce (equilibriumNetwork after) failedEdge)
      ≡ Load.zero (Network.localAlgebra algebra)

open DiscreteFractureTransition public

------------------------------------------------------------------------
-- The after-state already contains a complete finite equilibrium network, so
-- every vertex is re-equilibrated by construction.
------------------------------------------------------------------------

postFractureEquilibrium :
  {Scalar : Set}
  {vertexCount edgeCount : Nat}
  {algebra : Network.OrientedMechanicalAlgebra Scalar} →
  {before after : FractureMechanicalState algebra vertexCount edgeCount} →
  DiscreteFractureTransition algebra vertexCount edgeCount before after →
  (vertex : Fin.Fin vertexCount) →
  Load.add (Network.localAlgebra algebra)
    (Network.sumFin (Network.localAlgebra algebra) edgeCount
      (Network.signedContribution (equilibriumNetwork after) vertex))
    (Dim.magnitude
      (Network.externalForce (equilibriumNetwork after) vertex))
  ≡ Load.zero (Network.localAlgebra algebra)
postFractureEquilibrium {after = after} transition vertex =
  Network.equilibriumAt (equilibriumNetwork after) vertex

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data TensileThresholdExceededAutomaticallyFracturesEdge : Set where

tensileThresholdExceededDoesNotAutomaticallyFractureEdge :
  TensileThresholdExceededAutomaticallyFracturesEdge → ⊥
tensileThresholdExceededDoesNotAutomaticallyFractureEdge ()

data DiscreteEdgeFailureIsContinuumCrackPropagation : Set where

discreteEdgeFailureIsNotContinuumCrackPropagation :
  DiscreteEdgeFailureIsContinuumCrackPropagation → ⊥
discreteEdgeFailureIsNotContinuumCrackPropagation ()

data OneFractureStepDeterminesSubsequentFailureCascade : Set where

oneFractureStepDoesNotDetermineFailureCascade :
  OneFractureStepDeterminesSubsequentFailureCascade → ⊥
oneFractureStepDoesNotDetermineFailureCascade ()
