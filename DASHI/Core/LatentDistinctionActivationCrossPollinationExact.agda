module DASHI.Core.LatentDistinctionActivationCrossPollinationExact where

------------------------------------------------------------------------
-- LATENT-DISTINCTION ACTIVATION CROSS-POLLINATION
--
-- This file owns no new dynamic semantics.  It demonstrates that four existing
-- lanes inhabit the same canonical theorem shape:
--
--   ITIR hidden depth phase
--   nongin 1.0 -> 1.1 frame surfacing
--   TSFV/PNF semantic-query refinement
--   twistronics sourced registration control (conditional witness)
--
-- Shared shape does not identify mechanisms, semantics or authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Core.LatentDistinctionActivationExact as Activation
import DASHI.Cognition.PNF.TerminalisationDefectRegression as ITIR
import DASHI.Core.NonginOnePointOneFutureSplitExact as Nongin
import DASHI.Cognition.PNF.TSFVSemanticQueryFutureSplitExact as TSFV
import DASHI.Moonshine.TwistronicsRegistrationControlFutureSplitExact as TwistDynamic
import DASHI.Moonshine.TwistronicsRelativeRegistrationComparatorExact as Twist
import DASHI.Core.FutureSafeCoarseFibreCapacityExact as Capacity
import DASHI.Core.GeneralResidualFibreCardinalityExact as Cardinality

------------------------------------------------------------------------
-- 1. Existing concrete activations.
------------------------------------------------------------------------

itirHiddenDepthActivation :
  Activation.LatentDistinctionActivation
    ITIR.phaseSystem
    ITIR.phaseProjection
itirHiddenDepthActivation =
  ITIR.depthPhaseTerminalisationDefect

nonginFrameActivation :
  Activation.LatentDistinctionActivation
    Nongin.nonginFrameActionSystem
    Nongin.observeNongin
nonginFrameActivation =
  Nongin.nonginTerminalisationDefect

tsfvSemanticQueryActivation :
  Activation.LatentDistinctionActivation
    TSFV.semanticQueryActionSystem
    TSFV.observeQueryWorld
tsfvSemanticQueryActivation =
  TSFV.canonicalQueryTerminalisationDefect

------------------------------------------------------------------------
-- 2. The old ITIR fixture now gets the same residual-capacity theorem for free.
------------------------------------------------------------------------

itirHiddenDepthForcesResidualInjection :
  {Residual : Set} ->
  {residual : ITIR.PhaseState -> Residual} ->
  Capacity.FutureSafeResidual
    ITIR.phaseSystem
    ITIR.phaseProjection
    residual ->
  Cardinality.Injective
    (λ index ->
      residual
        (Activation.activationRepresentative
          itirHiddenDepthActivation
          index))
itirHiddenDepthForcesResidualInjection safe =
  Activation.activationForcesResidualInjection
    itirHiddenDepthActivation
    safe

itirHiddenDepthForcesBitCapacity :
  {bits : Nat} ->
  {residual : ITIR.PhaseState -> Cardinality.BitWords bits} ->
  Capacity.FutureSafeResidual
    ITIR.phaseSystem
    ITIR.phaseProjection
    residual ->
  2 ≤ Cardinality.pow2 bits
itirHiddenDepthForcesBitCapacity safe =
  Activation.activationForcesBitCapacity
    itirHiddenDepthActivation
    safe

nonginFrameForcesBitCapacity :
  {bits : Nat} ->
  {residual :
    Nongin.NonginDynamicState ->
    Cardinality.BitWords bits} ->
  Capacity.FutureSafeResidual
    Nongin.nonginFrameActionSystem
    Nongin.observeNongin
    residual ->
  2 ≤ Cardinality.pow2 bits
nonginFrameForcesBitCapacity safe =
  Activation.activationForcesBitCapacity
    nonginFrameActivation
    safe

tsfvSemanticQueryForcesBitCapacity :
  {bits : Nat} ->
  {residual :
    TSFV.QueryWorldState ->
    Cardinality.BitWords bits} ->
  Capacity.FutureSafeResidual
    TSFV.semanticQueryActionSystem
    TSFV.observeQueryWorld
    residual ->
  2 ≤ Cardinality.pow2 bits
tsfvSemanticQueryForcesBitCapacity safe =
  Activation.activationForcesBitCapacity
    tsfvSemanticQueryActivation
    safe

------------------------------------------------------------------------
-- 3. Twistronics is the same theorem shape once the evidence-gated
--    RegistrationControlSplitWitness is supplied.
------------------------------------------------------------------------

twistronicsControlActivation :
  ∀ {Microscopic Registration Effective}
    (system :
      Twist.RelativeRegistrationSystem
        Microscopic Registration Effective)
    (control : TwistDynamic.RegistrationControl Registration)
    (witness :
      TwistDynamic.RegistrationControlSplitWitness system control) ->
  Activation.LatentDistinctionActivation
    (TwistDynamic.registrationControlActionSystem control)
    (Twist.observeEffective system)
twistronicsControlActivation =
  TwistDynamic.registrationControlTerminalisationDefect

twistronicsControlForcesBitCapacity :
  ∀ {Microscopic Registration Effective bits}
    {system :
      Twist.RelativeRegistrationSystem
        Microscopic Registration Effective}
    {control : TwistDynamic.RegistrationControl Registration}
    (witness :
      TwistDynamic.RegistrationControlSplitWitness system control)
    {residual :
      Twist.OverlayState Microscopic Registration ->
      Cardinality.BitWords bits} ->
  Capacity.FutureSafeResidual
    (TwistDynamic.registrationControlActionSystem control)
    (Twist.observeEffective system)
    residual ->
  2 ≤ Cardinality.pow2 bits
twistronicsControlForcesBitCapacity witness safe =
  Activation.activationForcesBitCapacity
    (twistronicsControlActivation _ _ witness)
    safe

------------------------------------------------------------------------
-- 4. Typed convergence boundary.
------------------------------------------------------------------------

data ActivationLane : Set where
  itirHiddenPhaseLane : ActivationLane
  nonginFrameLane : ActivationLane
  tsfvSemanticQueryLane : ActivationLane
  twistronicsRegistrationControlLane : ActivationLane

record ActivationLaneStatus : Set where
  constructor activation-lane-status
  field
    lane : ActivationLane
    activationConstructed : Bool
    concreteWitnessConstructed : Bool
    capacityTheoremAvailable : Bool
    evidenceGated : Bool

canonicalITIRActivationStatus : ActivationLaneStatus
canonicalITIRActivationStatus =
  activation-lane-status
    itirHiddenPhaseLane
    true true true false

canonicalNonginActivationStatus : ActivationLaneStatus
canonicalNonginActivationStatus =
  activation-lane-status
    nonginFrameLane
    true true true false

canonicalTSFVActivationStatus : ActivationLaneStatus
canonicalTSFVActivationStatus =
  activation-lane-status
    tsfvSemanticQueryLane
    true true true false

canonicalTwistronicsActivationStatus : ActivationLaneStatus
canonicalTwistronicsActivationStatus =
  activation-lane-status
    twistronicsRegistrationControlLane
    true false true true

record LatentDistinctionCrossPollinationBoundary : Set where
  constructor latent-distinction-cross-pollination-boundary
  field
    commonActivationTheoremShape : Bool
    commonCapacityConsequence : Bool
    sharedShapeImpliesSharedMechanism : Bool
    sharedShapeImpliesSharedMechanismIsFalse :
      sharedShapeImpliesSharedMechanism ≡ false
    concreteFixtureImpliesEmpiricalUniversality : Bool
    concreteFixtureImpliesEmpiricalUniversalityIsFalse :
      concreteFixtureImpliesEmpiricalUniversality ≡ false
    twistronicsEvidenceGatePreserved : Bool

canonicalLatentDistinctionCrossPollinationBoundary :
  LatentDistinctionCrossPollinationBoundary
canonicalLatentDistinctionCrossPollinationBoundary =
  latent-distinction-cross-pollination-boundary
    true true
    false refl
    false refl
    true
