module DASHI.Wikimedia.SensibLawRateLimitedParallelGetterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.SensibLawSharedAcquisitionExecutionExact as Shared

------------------------------------------------------------------------
-- RATE-LIMITED PARALLEL GETTER
--
-- Runtime counterpart:
--   SensibLaw/src/sources/rate_limit.py::TokenBucketRateLimiter
--   SensibLaw/src/ontology/wikidata_nat_hf_partial_read.py
--
-- Concurrency and network-rate authority are deliberately different gates.
-- More worker slots never manufacture more rate permits.
------------------------------------------------------------------------

record LaunchPermit (workerSlotAvailable rateTokenAvailable : Bool) : Set where
  constructor launch-permit
  field
    workerGate : workerSlotAvailable ≡ true
    rateGate : rateTokenAvailable ≡ true
open LaunchPermit public

cannotLaunchWithoutWorkerSlot :
  {rateTokenAvailable : Bool} →
  LaunchPermit false rateTokenAvailable → ⊥
cannotLaunchWithoutWorkerSlot (launch-permit () _)

cannotLaunchWithoutRateToken :
  {workerSlotAvailable : Bool} →
  LaunchPermit workerSlotAvailable false → ⊥
cannotLaunchWithoutRateToken (launch-permit _ ())

------------------------------------------------------------------------
-- Execution receipt. These coordinates govern physical scheduling only.
------------------------------------------------------------------------

record ParallelGetterScheduleReceipt : Set where
  constructor parallel-getter-schedule-receipt
  field
    executionStrategy : String
    workerBudget : Nat
    peakInFlight : Nat
    sharedRateLimiterReference : String
    sharedAcrossWorkers : Bool
    sharedAcrossWorkersIsTrue : sharedAcrossWorkers ≡ true
    concurrencySafe : Bool
    concurrencySafeIsTrue : concurrencySafe ≡ true
    rateSafe : Bool
    rateSafeIsTrue : rateSafe ≡ true
    sourceSupportPaid : Bool
    sourceSupportPaidIsFalse : sourceSupportPaid ≡ false
open ParallelGetterScheduleReceipt public

natParallelGetterSchedule : ParallelGetterScheduleReceipt
natParallelGetterSchedule =
  parallel-getter-schedule-receipt
    "bounded_rate_limited_parallel"
    4
    4
    "SensibLaw src/sources/rate_limit.py TokenBucketRateLimiter"
    true refl
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Semantic observation surface excludes scheduler timing/order.
--
-- The Python runtime computes canonical_resolution_ref from exactly this kind
-- of surface: requested QIDs, resolved node IDs, earliest resolving chunks,
-- unresolved QIDs, language and non-creating probe semantics. Completion order,
-- worker IDs, peak concurrency and token timing do not enter this carrier.
------------------------------------------------------------------------

record CanonicalGetterObservation : Set where
  constructor canonical-getter-observation
  field
    requestedQidsReference : String
    resolvedQidsReference : String
    resolvedQidChunksReference : String
    qidRouteCacheSeedReference : String
    unresolvedQidsReference : String
    languageReference : String
    probeSemanticsReference : String
    canonicalResolutionReference : String
open CanonicalGetterObservation public

record GetterRun : Set where
  constructor getter-run
  field
    scheduleReceipt : ParallelGetterScheduleReceipt
    observation : CanonicalGetterObservation
open GetterRun public

-- Canonical semantic output is a function only of the observation carrier.
-- The schedule is intentionally erased at this boundary.
canonicalResult : GetterRun → CanonicalGetterObservation
canonicalResult run = observation run

sameObservationsImplySameCanonicalResult :
  (left right : GetterRun) →
  observation left ≡ observation right →
  canonicalResult left ≡ canonicalResult right
sameObservationsImplySameCanonicalResult left right same = same

-- Generic refinement form used when a downstream reducer maps the canonical
-- observation into a consumer-specific result.
rateLimitedParallelRefinesSerial :
  {Result : Set} →
  (reduce : CanonicalGetterObservation → Result) →
  (parallel serial : GetterRun) →
  observation parallel ≡ observation serial →
  reduce (canonicalResult parallel) ≡ reduce (canonicalResult serial)
rateLimitedParallelRefinesSerial reduce parallel serial refl = refl

------------------------------------------------------------------------
-- Shared-acquisition lineage: parallelism is an implementation strategy for
-- the already-existing shared Nat acquisition execution, not a new authority.
------------------------------------------------------------------------

record SharedParallelGetterReceipt
    (shared : Shared.SharedAcquisitionExecution) : Set where
  constructor shared-parallel-getter-receipt
  field
    getterSchedule : ParallelGetterScheduleReceipt
    sharedExecutionReference : String
    sharedExecutionReferenceExact :
      sharedExecutionReference ≡ Shared.sharedExecutionReceiptReference shared
    canonicalObservationReference : String
    consumerVerificationPerformed : Bool
    consumerVerificationPerformedIsFalse :
      consumerVerificationPerformed ≡ false
    semanticPromotionPerformed : Bool
    semanticPromotionPerformedIsFalse : semanticPromotionPerformed ≡ false
open SharedParallelGetterReceipt public

natSharedParallelGetterReceipt :
  SharedParallelGetterReceipt Shared.natSharedSourceSupportExecution
natSharedParallelGetterReceipt =
  shared-parallel-getter-receipt
    natParallelGetterSchedule
    "one union transport execution receipt"
    refl
    "runtime canonical_resolution_ref"
    false refl
    false refl

------------------------------------------------------------------------
-- Hard firewalls.
------------------------------------------------------------------------

data MoreWorkersCreateMoreRateAuthority : Set where
data ParallelCompletionOrderCreatesSemanticAuthority : Set where
data GetterExecutionPaysSourceSupport : Set where
data CanonicalResolutionCreatesPromotionAuthority : Set where

moreWorkersDoNotCreateMoreRateAuthority :
  MoreWorkersCreateMoreRateAuthority → ⊥
moreWorkersDoNotCreateMoreRateAuthority ()

completionOrderDoesNotCreateSemanticAuthority :
  ParallelCompletionOrderCreatesSemanticAuthority → ⊥
completionOrderDoesNotCreateSemanticAuthority ()

getterExecutionDoesNotPaySourceSupport : GetterExecutionPaysSourceSupport → ⊥
getterExecutionDoesNotPaySourceSupport ()

canonicalResolutionDoesNotCreatePromotionAuthority :
  CanonicalResolutionCreatesPromotionAuthority → ⊥
canonicalResolutionDoesNotCreatePromotionAuthority ()

------------------------------------------------------------------------
-- Runtime/formal contract exported to the SensibLaw implementation.
------------------------------------------------------------------------

record RateLimitedParallelGetterContract : Set where
  constructor rate-limited-parallel-getter-contract
  field
    oneSharedLimiterAcrossWorkers : Bool
    workerAndRatePermitsAreDistinct : Bool
    completionOrderErasedBeforeCanonicalReduction : Bool
    earliestResolvingChunkOwnsCanonicalRouteSeed : Bool
    higherThanSerialFrontierMayBeCancelled : Bool
    sameObservationSurfaceImpliesSameConsumerResult : Bool
    schedulerCreatesSourceAuthority : Bool
    schedulerCreatesPromotionAuthority : Bool

canonicalRateLimitedParallelGetterContract : RateLimitedParallelGetterContract
canonicalRateLimitedParallelGetterContract =
  rate-limited-parallel-getter-contract
    true true true true true true false false
