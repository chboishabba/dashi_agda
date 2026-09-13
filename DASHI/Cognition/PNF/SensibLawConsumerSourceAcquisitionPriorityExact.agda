module DASHI.Cognition.PNF.SensibLawConsumerSourceAcquisitionPriorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic

------------------------------------------------------------------------
-- CONSUMER-SENSITIVE SOURCE ACQUISITION PRIORITY
--
-- An unresolved legal/source coordinate is not automatically a live source
-- acquisition demand.  Applications must distinguish:
--   * coordinates capable of changing the selected live consumer now;
--   * coordinates relevant only to an explicit counterfactual consumer;
--   * coordinates downstream of a source-conditioned atomic failure;
--   * optional enrichment not required by either selected consumer.
--
-- This is an admission layer above the existing generic scheduler/bound-demand
-- machinery.  It does not replace those owners and does not claim that a
-- deferred coordinate is legally irrelevant in every possible query.
------------------------------------------------------------------------

record ConsumerSourcePolicy : Set₁ where
  constructor consumer-source-policy
  field
    Consumer Coordinate : Set
    liveSensitive : Consumer → Coordinate → Set
    counterfactualSensitive : Consumer → Coordinate → Set
    policyReference : String

open ConsumerSourcePolicy public

record UpstreamAtomicBlocker
    (policy : ConsumerSourcePolicy)
    (consumer : Consumer policy)
    (coordinate : Coordinate policy) : Set₁ where
  constructor upstream-atomic-blocker
  field
    blockerProposition : Algebra.LegalProposition
    blockerTest : Atomic.SourceConditionedAtomicLegalTest blockerProposition
    blockerGateIsNegative : Atomic.gate blockerTest ≡ BT.neg
    blocksLiveSensitivity : liveSensitive policy consumer coordinate → ⊥
    blockerReference : String

open UpstreamAtomicBlocker public

data SourceAcquisitionDisposition
    (policy : ConsumerSourcePolicy)
    (consumer : Consumer policy)
    (coordinate : Coordinate policy) : Set₁ where

  acquireForLiveConsumer :
    liveSensitive policy consumer coordinate →
    SourceAcquisitionDisposition policy consumer coordinate

  deferForCounterfactualConsumer :
    (liveSensitive policy consumer coordinate → ⊥) →
    counterfactualSensitive policy consumer coordinate →
    SourceAcquisitionDisposition policy consumer coordinate

  blockedDownstream :
    UpstreamAtomicBlocker policy consumer coordinate →
    SourceAcquisitionDisposition policy consumer coordinate

  optionalEnrichment :
    (liveSensitive policy consumer coordinate → ⊥) →
    (counterfactualSensitive policy consumer coordinate → ⊥) →
    SourceAcquisitionDisposition policy consumer coordinate

------------------------------------------------------------------------
-- Only a live-consumer sensitivity witness confers permission to promote the
-- coordinate into the present acquisition queue.  Counterfactual/deferred and
-- blocked coordinates remain typed coordinates, but do not consume the live
-- consumer's source-search budget merely because they are unresolved.
------------------------------------------------------------------------

data AcquireNowPermission
    (policy : ConsumerSourcePolicy)
    (consumer : Consumer policy)
    (coordinate : Coordinate policy) : Set₁ where
  acquire-now :
    liveSensitive policy consumer coordinate →
    AcquireNowPermission policy consumer coordinate

permissionFromLiveDisposition :
  ∀ {policy consumer coordinate} →
  liveSensitive policy consumer coordinate →
  AcquireNowPermission policy consumer coordinate
permissionFromLiveDisposition = acquire-now

blockedCoordinateHasNoLiveSensitivity :
  ∀ {policy consumer coordinate} →
  UpstreamAtomicBlocker policy consumer coordinate →
  liveSensitive policy consumer coordinate → ⊥
blockedCoordinateHasNoLiveSensitivity blocker = blocksLiveSensitivity blocker

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data UnresolvedCoordinateAutomaticallyAcquireNow : Set where
data CounterfactualSensitivityMeansLiveSensitivity : Set where
data AtomicNegativeMeansCoordinateIrrelevantForever : Set where
data DeferredCoordinateMayBeDeletedFromOntology : Set where
data FamilyRecognitionForcesDownstreamAcquisition : Set where

unresolvedDoesNotAutoEnterLiveQueue :
  UnresolvedCoordinateAutomaticallyAcquireNow → ⊥
unresolvedDoesNotAutoEnterLiveQueue ()

counterfactualDoesNotBecomeLiveByDefault :
  CounterfactualSensitivityMeansLiveSensitivity → ⊥
counterfactualDoesNotBecomeLiveByDefault ()

atomicBlockerIsConsumerRelativeNotEternalIrrelevance :
  AtomicNegativeMeansCoordinateIrrelevantForever → ⊥
atomicBlockerIsConsumerRelativeNotEternalIrrelevance ()

deferredCoordinateRemainsTyped : DeferredCoordinateMayBeDeletedFromOntology → ⊥
deferredCoordinateRemainsTyped ()

familyRecognitionDoesNotForceEveryDownstreamSearch :
  FamilyRecognitionForcesDownstreamAcquisition → ⊥
familyRecognitionDoesNotForceEveryDownstreamSearch ()

record ConsumerSourceAcquisitionPriorityBoundary : Set where
  constructor consumer-source-acquisition-priority-boundary
  field
    unresolvedAutomaticallyMeansAcquireNow : Bool
    liveConsumerSensitivityRequiredForAcquireNow : Bool
    counterfactualCoordinateMayRemainUnresolved : Bool
    atomicNegativeMayBlockDownstreamForSelectedConsumer : Bool
    blockedCoordinateIsIrrelevantForEveryConsumerForever : Bool
    deferredCoordinateMayBeErased : Bool

canonicalConsumerSourceAcquisitionPriorityBoundary :
  ConsumerSourceAcquisitionPriorityBoundary
canonicalConsumerSourceAcquisitionPriorityBoundary =
  consumer-source-acquisition-priority-boundary
    false true true true false false
