module DASHI.Physics.Quantum.CircularRydbergYangMillsSimulationAuthorityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Physics.Closure.QuantumDecoherenceAdmissibilityConcentration as Decoherence
import DASHI.Physics.Quantum.CircularRydbergRoomTemperatureLifetimeExact as Rydberg
import DASHI.Physics.YangMills.BalabanYangMillsGapAuthorityHierarchyExact as YM

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- A longer-lived neutral-atom platform can enlarge an experimental simulation
-- window, but lifetime is not an encoding of a target Hamiltonian and is not a
-- Yang--Mills mass-gap theorem.  The source paper supplies platform evidence;
-- the target model, approximation/error control and simulation-time relation
-- remain separate consumer obligations.
--
-- This file also imports the generic quantum-decoherence interpretation and
-- the existing YM authority hierarchy.  The import is intentionally one-way:
-- neither generic decoherence structure nor the Rydberg paper is promoted into
-- a concrete YM gap witness.
------------------------------------------------------------------------

data PlatformLifetimeClass : Set where
  longLivedCircularRydbergWindow : PlatformLifetimeClass

data TargetHamiltonianClass : Set where
  targetSpinModel : TargetHamiltonianClass
  targetGaugeModel : TargetHamiltonianClass

data SimulatorWorld : Set where
  sameLifetimeSpinWorld : SimulatorWorld
  sameLifetimeGaugeWorld : SimulatorWorld

lifetimeProjection : SimulatorWorld → PlatformLifetimeClass
lifetimeProjection sameLifetimeSpinWorld = longLivedCircularRydbergWindow
lifetimeProjection sameLifetimeGaugeWorld = longLivedCircularRydbergWindow

targetHamiltonianProjection : SimulatorWorld → TargetHamiltonianClass
targetHamiltonianProjection sameLifetimeSpinWorld = targetSpinModel
targetHamiltonianProjection sameLifetimeGaugeWorld = targetGaugeModel

targetHamiltoniansDiffer :
  targetHamiltonianProjection sameLifetimeSpinWorld
  ≡ targetHamiltonianProjection sameLifetimeGaugeWorld → ⊥
targetHamiltoniansDiffer ()

lifetimeHamiltonianCollision :
  INF.NonFactorabilityWitness lifetimeProjection targetHamiltonianProjection
lifetimeHamiltonianCollision =
  INF.nonFactorabilityWitness
    sameLifetimeSpinWorld
    sameLifetimeGaugeWorld
    refl
    targetHamiltoniansDiffer

lifetimeDoesNotDetermineHamiltonian :
  INF.FactorsThrough lifetimeProjection targetHamiltonianProjection → ⊥
lifetimeDoesNotDetermineHamiltonian =
  INF.witnessRulesOutEveryFlatFactorisation lifetimeHamiltonianCollision

------------------------------------------------------------------------
-- Independently, platform lifetime cannot determine the YM authority level.
-- The worlds below are synthetic countermodels for factorisation only.  They
-- do not assert that the Rydberg experiment realizes either YM authority.
------------------------------------------------------------------------

data AuthorityWorld : Set where
  longLifetimeFiniteAuthorityWorld : AuthorityWorld
  longLifetimeOSAuthorityWorld : AuthorityWorld

authorityLifetimeProjection : AuthorityWorld → PlatformLifetimeClass
authorityLifetimeProjection longLifetimeFiniteAuthorityWorld =
  longLivedCircularRydbergWindow
authorityLifetimeProjection longLifetimeOSAuthorityWorld =
  longLivedCircularRydbergWindow

yangMillsAuthorityProjection : AuthorityWorld → YM.GapAuthorityLabel
yangMillsAuthorityProjection longLifetimeFiniteAuthorityWorld =
  YM.finiteBackgroundGaussian
yangMillsAuthorityProjection longLifetimeOSAuthorityWorld =
  YM.osHamiltonianSpectral

yangMillsAuthoritiesDiffer :
  yangMillsAuthorityProjection longLifetimeFiniteAuthorityWorld
  ≡ yangMillsAuthorityProjection longLifetimeOSAuthorityWorld → ⊥
yangMillsAuthoritiesDiffer = YM.finiteIsNotOS

lifetimeYangMillsAuthorityCollision :
  INF.NonFactorabilityWitness
    authorityLifetimeProjection
    yangMillsAuthorityProjection
lifetimeYangMillsAuthorityCollision =
  INF.nonFactorabilityWitness
    longLifetimeFiniteAuthorityWorld
    longLifetimeOSAuthorityWorld
    refl
    yangMillsAuthoritiesDiffer

longLifetimeDoesNotProduceYangMillsGap :
  INF.FactorsThrough
    authorityLifetimeProjection
    yangMillsAuthorityProjection → ⊥
longLifetimeDoesNotProduceYangMillsGap =
  INF.witnessRulesOutEveryFlatFactorisation
    lifetimeYangMillsAuthorityCollision

------------------------------------------------------------------------
-- Positive bridge for a bounded analogue/digital quantum-simulation claim.
-- All target-specific obligations must be supplied explicitly.
------------------------------------------------------------------------

record TargetHamiltonianSimulationBridge : Set₁ where
  field
    platformEvidence : Rydberg.CircularRydbergExperimentalClaimSurface
    targetHamiltonianIdentity : String
    targetDynamicsIdentity : String

    encodingWitness : Set
    approximationErrorBudget : Set
    simulationTimeWithinPlatformWindow : Set
    preparationAndReadoutAdequacy : Set

    -- If a consumer wants to interpret environmental interaction using the
    -- generic concentration/decoherence calculus, it must provide that model;
    -- the Rydberg source does not manufacture it.
    optionalConcreteDecoherenceModel : Set

open TargetHamiltonianSimulationBridge public

encodedSimulationRequiresBridge :
  (bridge : TargetHamiltonianSimulationBridge) → Set
encodedSimulationRequiresBridge bridge = encodingWitness bridge

errorControlledSimulationRequiresBudget :
  (bridge : TargetHamiltonianSimulationBridge) → Set
errorControlledSimulationRequiresBudget bridge = approximationErrorBudget bridge

timeBoundedSimulationRequiresWindow :
  (bridge : TargetHamiltonianSimulationBridge) → Set
timeBoundedSimulationRequiresWindow bridge =
  simulationTimeWithinPlatformWindow bridge

------------------------------------------------------------------------
-- Explicit no-promotion token: even an inhabited simulator bridge carries no
-- constructor that yields YM.OSReconstructedHamiltonianGap.  A separate YM
-- theorem chain is still required by the existing hierarchy.
------------------------------------------------------------------------

data RydbergSimulationImpliesOSYangMillsGap : Set where

rydbergSimulationCannotAutoPromoteToOSGap :
  RydbergSimulationImpliesOSYangMillsGap → ⊥
rydbergSimulationCannotAutoPromoteToOSGap ()

-- Keep the generic decoherence owner visibly in the dependency graph without
-- pretending the source paper instantiates it.
ConcreteDecoherenceModel : Set₃
ConcreteDecoherenceModel = Decoherence.DecoherenceAsAdmissibilityConcentration
