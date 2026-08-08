module DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyContinuationRound27Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Isolate the exact finite-dimensional continuation reducer.  A Galerkin
-- energy identity supplies an explicit nonnegative slack between the current
-- energy and the initial energy.  A normed finite-dimensional continuation
-- theorem may consume precisely this bounded-energy witness; it no longer
-- receives an unrelated boundedness receipt.
--
-- The local Picard--Lindelof theorem over the repository's eventual real
-- coordinate backend remains an external analytic producer.  This file proves
-- the exact bridge from the physical energy identity to its continuation
-- hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _,_; _×_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _≤_)

zeroQ : ℚ
zeroQ = Int.+ 0 / 1

record FiniteGalerkinEnergyTrajectory : Set₁ where
  field
    Time State : Set
    initialTime : Time
    stateAt : Time → State
    energy : State → ℚ
    accumulatedDissipation : Time → ℚ
    initialDissipationZero : accumulatedDissipation initialTime ≡ zeroQ
    dissipationNonnegative :
      (time : Time) → zeroQ ≤ accumulatedDissipation time
    energyIdentity :
      (time : Time) →
      energy (stateAt time) + accumulatedDissipation time
      ≡ energy (stateAt initialTime)

open FiniteGalerkinEnergyTrajectory public

record EnergyBoundWitness
    (trajectory : FiniteGalerkinEnergyTrajectory)
    (time : Time trajectory) : Set where
  constructor energy-bound-witness
  field
    slack : ℚ
    slackNonnegative : zeroQ ≤ slack
    boundEquation :
      energy trajectory (stateAt trajectory time) + slack
      ≡ energy trajectory (stateAt trajectory (initialTime trajectory))

open EnergyBoundWitness public

energyIdentityConstructsBoundWitness :
  (trajectory : FiniteGalerkinEnergyTrajectory) →
  (time : Time trajectory) →
  EnergyBoundWitness trajectory time
energyIdentityConstructsBoundWitness trajectory time =
  energy-bound-witness
    (accumulatedDissipation trajectory time)
    (dissipationNonnegative trajectory time)
    (energyIdentity trajectory time)

record FiniteContinuationRule
    (trajectory : FiniteGalerkinEnergyTrajectory) : Set₁ where
  field
    Extension : Time trajectory → Set
    extendFromEnergyBound :
      (time : Time trajectory) →
      EnergyBoundWitness trajectory time →
      Extension time

open FiniteContinuationRule public

energyControlledFiniteContinuation :
  (trajectory : FiniteGalerkinEnergyTrajectory) →
  (rule : FiniteContinuationRule trajectory) →
  (time : Time trajectory) →
  Extension rule time
energyControlledFiniteContinuation trajectory rule time =
  extendFromEnergyBound rule time
    (energyIdentityConstructsBoundWitness trajectory time)

record FiniteEnergyContinuationBoundary : Set where
  constructor finite-energy-continuation-boundary
  field
    energyIdentityConnectedToContinuationHypothesis :
      Agda.Builtin.Bool.Bool
    energyIdentityConnectedToContinuationHypothesisIsTrue :
      energyIdentityConnectedToContinuationHypothesis
      ≡ Agda.Builtin.Bool.true
    repositoryRealPicardLindelofInstantiated : Agda.Builtin.Bool.Bool
    repositoryRealPicardLindelofInstantiatedIsFalse :
      repositoryRealPicardLindelofInstantiated
      ≡ Agda.Builtin.Bool.false

canonicalFiniteEnergyContinuationBoundary : FiniteEnergyContinuationBoundary
canonicalFiniteEnergyContinuationBoundary =
  finite-energy-continuation-boundary
    Agda.Builtin.Bool.true refl Agda.Builtin.Bool.false refl
