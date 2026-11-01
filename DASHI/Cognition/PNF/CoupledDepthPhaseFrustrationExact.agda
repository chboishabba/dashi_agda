module DASHI.Cognition.PNF.CoupledDepthPhaseFrustrationExact where

------------------------------------------------------------------------
-- COUPLED C3 PHASE FRUSTRATION
--
-- Finite exact seed for the multi-fibre hyperfabric proposal.  Different PNF
-- fibres may share semantic provenance while occupying different depth/learning
-- phases.  This module formalises only the phase-coupling mathematics; it does
-- not identify the energy below with a biological or clinical energy.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_+_; _*_; _≤_; z≤n)

import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

one : Nat
one = suc zero

phaseDisagreement :
  Wheel.DepthWheelPhase → Wheel.DepthWheelPhase → Nat
phaseDisagreement Wheel.phase-0 Wheel.phase-0 = zero
phaseDisagreement Wheel.phase-0 Wheel.phase-1 = one
phaseDisagreement Wheel.phase-0 Wheel.phase-2 = one
phaseDisagreement Wheel.phase-1 Wheel.phase-0 = one
phaseDisagreement Wheel.phase-1 Wheel.phase-1 = zero
phaseDisagreement Wheel.phase-1 Wheel.phase-2 = one
phaseDisagreement Wheel.phase-2 Wheel.phase-0 = one
phaseDisagreement Wheel.phase-2 Wheel.phase-1 = one
phaseDisagreement Wheel.phase-2 Wheel.phase-2 = zero

phaseDisagreementReflexiveZero :
  (phase : Wheel.DepthWheelPhase) →
  phaseDisagreement phase phase ≡ zero
phaseDisagreementReflexiveZero Wheel.phase-0 = refl
phaseDisagreementReflexiveZero Wheel.phase-1 = refl
phaseDisagreementReflexiveZero Wheel.phase-2 = refl

phaseDisagreementSymmetric :
  (left right : Wheel.DepthWheelPhase) →
  phaseDisagreement left right ≡ phaseDisagreement right left
phaseDisagreementSymmetric Wheel.phase-0 Wheel.phase-0 = refl
phaseDisagreementSymmetric Wheel.phase-0 Wheel.phase-1 = refl
phaseDisagreementSymmetric Wheel.phase-0 Wheel.phase-2 = refl
phaseDisagreementSymmetric Wheel.phase-1 Wheel.phase-0 = refl
phaseDisagreementSymmetric Wheel.phase-1 Wheel.phase-1 = refl
phaseDisagreementSymmetric Wheel.phase-1 Wheel.phase-2 = refl
phaseDisagreementSymmetric Wheel.phase-2 Wheel.phase-0 = refl
phaseDisagreementSymmetric Wheel.phase-2 Wheel.phase-1 = refl
phaseDisagreementSymmetric Wheel.phase-2 Wheel.phase-2 = refl

pairFrustration :
  Nat → Wheel.DepthWheelPhase → Wheel.DepthWheelPhase → Nat
pairFrustration weight left right =
  weight * phaseDisagreement left right

threeFibreFrustration :
  Nat → Nat → Nat →
  Wheel.DepthWheelPhase →
  Wheel.DepthWheelPhase →
  Wheel.DepthWheelPhase → Nat
threeFibreFrustration weightAB weightBC weightCA a b c =
  pairFrustration weightAB a b
  + pairFrustration weightBC b c
  + pairFrustration weightCA c a

synchronisedThreeFibreCostZero :
  (weightAB weightBC weightCA : Nat)
  (phase : Wheel.DepthWheelPhase) →
  threeFibreFrustration weightAB weightBC weightCA phase phase phase ≡ zero
synchronisedThreeFibreCostZero weightAB weightBC weightCA Wheel.phase-0 = refl
synchronisedThreeFibreCostZero weightAB weightBC weightCA Wheel.phase-1 = refl
synchronisedThreeFibreCostZero weightAB weightBC weightCA Wheel.phase-2 = refl

frustrationNonnegative :
  (weightAB weightBC weightCA : Nat)
  (a b c : Wheel.DepthWheelPhase) →
  zero ≤ threeFibreFrustration weightAB weightBC weightCA a b c
frustrationNonnegative weightAB weightBC weightCA a b c = z≤n

------------------------------------------------------------------------
-- Zero is therefore a certified global lower bound, and every synchronized
-- phase configuration attains it.  Persistent nonzero minima require a
-- restricted reachability/update graph; that belongs in the dynamical layer,
-- not in this bare finite cost function.
------------------------------------------------------------------------

synchronisedAttainsGlobalLowerBound :
  (weightAB weightBC weightCA : Nat)
  (phase : Wheel.DepthWheelPhase)
  (a b c : Wheel.DepthWheelPhase) →
  threeFibreFrustration weightAB weightBC weightCA phase phase phase
  ≤ threeFibreFrustration weightAB weightBC weightCA a b c
synchronisedAttainsGlobalLowerBound weightAB weightBC weightCA phase a b c
  rewrite synchronisedThreeFibreCostZero weightAB weightBC weightCA phase = z≤n
