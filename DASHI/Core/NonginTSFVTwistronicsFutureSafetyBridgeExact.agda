module DASHI.Core.NonginTSFVTwistronicsFutureSafetyBridgeExact where

------------------------------------------------------------------------
-- NONGIN / TSFV / TWISTRONICS FUTURE-SAFETY BRIDGE
--
-- Present-state non-descent is already proved in all three lanes:
--
--   nongin      : frame-sensitive consumer cannot descend through 1.0;
--   TSFV        : history-sensitive choice cannot descend through the coarse
--                 caustic observation;
--   twistronics : registration-sensitive effective observation cannot descend
--                 through the microscopic-pair projection.
--
-- FutureSafeCoarseFibreCapacityExact gives the dynamic theorem once an
-- application supplies a proof-bearing action system and a finite set of
-- future-distinct representatives.
--
-- Nongin and the TSFV/PNF semantic-query lane now supply concrete
-- proof-bearing dynamic fixtures.  Twistronics now supplies a sourced physical
-- registration-control action system and a generic future-split theorem gated
-- by an explicit control-sensitive witness.  The physical TSFV
-- caustic/history-realization lane remains a separate obligation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.NonginOnePointOneArmyRefinementExact as Nongin
import DASHI.Core.NonginOnePointOneFutureSplitExact as NonginDynamic
import DASHI.Physics.Closure.TSFVHistoryConditionedChoiceBridgeExact as TSFV
import DASHI.Cognition.PNF.TSFVSemanticQueryFutureSplitExact as TSFVDynamic
import DASHI.Physics.Closure.TSFVBidirectionalCausticBridgeExact as TSFVCaustic
import DASHI.Moonshine.TwistronicsRelativeRegistrationComparatorExact as Twist
import DASHI.Moonshine.TwistronicsRegistrationControlFutureSplitExact as TwistDynamic
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Base
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.FutureSafeCoarseFibreCapacityExact as FutureCapacity
import DASHI.Core.ConsumerGuidedReopenableRefinementExact as Refine

------------------------------------------------------------------------
-- 1. Existing current-consumer failures of descent.
------------------------------------------------------------------------

nonginCurrentConsumerCannotDescend :
  Base.ConsumerDescent
    (Nongin.onePointZeroProject {Nongin.Base1} {Nongin.Frame2})
    Nongin.frameSensitiveResponse ->
  ⊥
nonginCurrentConsumerCannotDescend =
  Nongin.onePointZeroCannotServeEveryFrameSensitiveConsumer
    Nongin.canonicalFrameSensitiveConsumer

tsfvCurrentConsumerCannotDescend :
  NonFactor.FactorsThrough
    TSFVCaustic.historyProjection
    TSFV.historySensitiveChoice ->
  ⊥
tsfvCurrentConsumerCannotDescend =
  TSFV.causticProjectionInsufficientForHistorySensitiveChoice

twistronicsCurrentConsumerCannotDescend :
  {Microscopic Registration Effective : Set} ->
  (system : Twist.RelativeRegistrationSystem Microscopic Registration Effective) ->
  (witness : Twist.RegistrationSensitiveWitness system) ->
  Base.ConsumerDescent
    Twist.forgetRegistration
    (Twist.observeEffective system) ->
  ⊥
twistronicsCurrentConsumerCannotDescend =
  Twist.coarseMicroscopicPairCannotServeRegistrationSensitiveConsumer

------------------------------------------------------------------------
-- 2. Generic dynamic handoff.
--
-- Any application may supply a DependentActionSystem, use the same coarse
-- observer, prove finite representatives future-distinct under the canonical
-- FutureEquivalent relation, and then consume the exact capacity theorem.
------------------------------------------------------------------------

futureSafeCapacityOwnerPresent :
  FutureCapacity.FutureSafeCoarseFibreCapacityBoundary
futureSafeCapacityOwnerPresent =
  FutureCapacity.canonicalFutureSafeCoarseFibreCapacityBoundary

------------------------------------------------------------------------
-- 3. Domain status: current theorem versus dynamic obligation.
------------------------------------------------------------------------

data DomainLane : Set where
  nonginFrameLane : DomainLane
  tsfvHistoryLane : DomainLane
  tsfvSemanticQueryLane : DomainLane
  twistronicsRegistrationLane : DomainLane

record DomainFutureSafetyStatus : Set where
  constructor domain-future-safety-status
  field
    lane : DomainLane
    currentConsumerNonDescentProved : Bool
    strictOrNonfactorableRefinementProved : Bool
    proofBearingActionSystemSuppliedHere : Bool
    finiteFutureDistinctFibreSuppliedHere : Bool
    concreteFutureCapacityBoundInstantiatedHere : Bool
    nextObligation : String

canonicalNonginFutureSafetyStatus : DomainFutureSafetyStatus
canonicalNonginFutureSafetyStatus =
  domain-future-safety-status
    nonginFrameLane
    true true
    true true true
    "concrete 1.0-to-1.1 surface-frame future split and two-class capacity theorem are instantiated in NonginOnePointOneFutureSplitExact"

canonicalTSFVFutureSafetyStatus : DomainFutureSafetyStatus
canonicalTSFVFutureSafetyStatus =
  domain-future-safety-status
    tsfvHistoryLane
    true true
    false false false
    "bind the existing admissible-history/world machinery to a DependentActionSystem whose common traces expose history-sensitive future observations"


canonicalTSFVSemanticQueryFutureSafetyStatus : DomainFutureSafetyStatus
canonicalTSFVSemanticQueryFutureSafetyStatus =
  domain-future-safety-status
    tsfvSemanticQueryLane
    true true
    true true true
    "semantic-query future split is concretely instantiated; physical caustic History3-to-Candidate256 realization remains a separate sourced obligation"

canonicalTwistronicsFutureSafetyStatus : DomainFutureSafetyStatus
canonicalTwistronicsFutureSafetyStatus =
  domain-future-safety-status
    twistronicsRegistrationLane
    true true
    true false false
    "physical in-situ twist control action system is sourced and constructed; instantiate RegistrationControlSplitWitness only when an exact equal-before / unequal-after effective-observation pair is established"

------------------------------------------------------------------------
-- 4. Cross-domain firewall.
------------------------------------------------------------------------

record NonginTSFVTwistronicsFutureSafetyBoundary : Set where
  constructor nongin-tsfv-twistronics-future-safety-boundary
  field
    sharedCurrentNonDescentShape : Bool
    sharedFutureCapacityTheoremAvailable : Bool
    nonginDynamicsAlreadyConstructed : Bool
    tsfvSemanticQueryDynamicsConstructed : Bool
    tsfvCausticHistoryDynamicsConstructed : Bool
    twistronicsDynamicsAlreadyConstructed : Bool
    currentNonDescentImpliesFutureDistinctionAutomatically : Bool
    currentNonDescentImpliesFutureDistinctionAutomaticallyIsFalse :
      currentNonDescentImpliesFutureDistinctionAutomatically ≡ false
    sharedShapeImpliesSharedPhysicalMechanism : Bool
    sharedShapeImpliesSharedPhysicalMechanismIsFalse :
      sharedShapeImpliesSharedPhysicalMechanism ≡ false

canonicalNonginTSFVTwistronicsFutureSafetyBoundary :
  NonginTSFVTwistronicsFutureSafetyBoundary
canonicalNonginTSFVTwistronicsFutureSafetyBoundary =
  nongin-tsfv-twistronics-future-safety-boundary
    true true
    true true false true
    false refl
    false refl
