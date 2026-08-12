module DASHI.Cognition.PNF.RestrictedConstraintMetastabilityExact where

------------------------------------------------------------------------
-- RESTRICTED-REACHABILITY METASTABILITY
--
-- ConstraintNetworkObstructionExact proves that the C3 triangle has global
-- minimum frustration 1.  Here we add a local update graph.  Only phase A may
-- advance; phases B and C are frozen.  The state (0,1,2) has cost 2 and its
-- only one-step successor also has cost 2, while the global cost-1 witness
-- (0,0,0) is unreachable because B and C are invariants.
--
-- This is the missing dynamical distinction: a non-global persistent basin is
-- caused by restricted reachability, not by merely naming an energy.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

import DASHI.Cognition.PNF.ConstraintNetworkObstructionExact as Network
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

advanceA : Network.TriangleAssignment → Network.TriangleAssignment
advanceA assignment =
  Network.triangleAssignment
    (Wheel.nextDepthWheelPhase (Network.phaseA assignment))
    (Network.phaseB assignment)
    (Network.phaseC assignment)

data RestrictedReachable :
    Network.TriangleAssignment → Network.TriangleAssignment → Set where
  restrictedRefl :
    ∀ {state} → RestrictedReachable state state
  restrictedStep :
    ∀ {before after} →
    RestrictedReachable (advanceA before) after →
    RestrictedReachable before after

phaseBInvariant :
  ∀ {before after} →
  RestrictedReachable before after →
  Network.phaseB before ≡ Network.phaseB after
phaseBInvariant restrictedRefl = refl
phaseBInvariant (restrictedStep path) = phaseBInvariant path

phaseCInvariant :
  ∀ {before after} →
  RestrictedReachable before after →
  Network.phaseC before ≡ Network.phaseC after
phaseCInvariant restrictedRefl = refl
phaseCInvariant (restrictedStep path) = phaseCInvariant path

metastableState : Network.TriangleAssignment
metastableState =
  Network.triangleAssignment Wheel.phase-0 Wheel.phase-1 Wheel.phase-2

globalMinimumWitness : Network.TriangleAssignment
globalMinimumWitness =
  Network.triangleAssignment Wheel.phase-0 Wheel.phase-0 Wheel.phase-0

metastableCostIsTwo :
  Network.triangleFrustration metastableState ≡ 2
metastableCostIsTwo = refl

oneRestrictedStepPreservesCost :
  Network.triangleFrustration (advanceA metastableState)
  ≡ Network.triangleFrustration metastableState
oneRestrictedStepPreservesCost = refl

record OneStepLocalMinimum (state : Network.TriangleAssignment) : Set where
  constructor oneStepLocalMinimum
  field
    successorNotLower :
      Network.triangleFrustration state
      ≤ Network.triangleFrustration (advanceA state)

open OneStepLocalMinimum public

metastableIsOneStepLocalMinimum : OneStepLocalMinimum metastableState
metastableIsOneStepLocalMinimum =
  oneStepLocalMinimum (s≤s (s≤s z≤n))

globalWitnessCostIsOne :
  Network.triangleFrustration globalMinimumWitness ≡ 1
globalWitnessCostIsOne = Network.costOneWitness

phaseOneNotPhaseZero : Wheel.phase-1 ≡ Wheel.phase-0 → ⊥
phaseOneNotPhaseZero ()

globalMinimumUnreachableFromMetastable :
  RestrictedReachable metastableState globalMinimumWitness → ⊥
globalMinimumUnreachableFromMetastable path =
  phaseOneNotPhaseZero (phaseBInvariant path)

record RestrictedMetastabilityWitness : Set where
  constructor restrictedMetastabilityWitness
  field
    trappedState : Network.TriangleAssignment
    lowerState : Network.TriangleAssignment
    trappedCost : Network.triangleFrustration trappedState ≡ 2
    lowerCost : Network.triangleFrustration lowerState ≡ 1
    trappedIsLocalMinimum : OneStepLocalMinimum trappedState
    lowerStateUnreachable : RestrictedReachable trappedState lowerState → ⊥

open RestrictedMetastabilityWitness public

canonicalRestrictedMetastability : RestrictedMetastabilityWitness
canonicalRestrictedMetastability =
  restrictedMetastabilityWitness
    metastableState
    globalMinimumWitness
    metastableCostIsTwo
    globalWitnessCostIsOne
    metastableIsOneStepLocalMinimum
    globalMinimumUnreachableFromMetastable
