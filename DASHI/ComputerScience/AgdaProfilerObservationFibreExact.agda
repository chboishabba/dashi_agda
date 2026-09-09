{-# OPTIONS --safe #-}
module DASHI.ComputerScience.AgdaProfilerObservationFibreExact where

------------------------------------------------------------------------
-- AGDA 2.9 PROFILER OBSERVATION FIBRE
--
-- Agda's --profile surface is an observer over a checker run.  It does not
-- change theorem meaning and its output is empirical diagnostic evidence, not
-- a proof inhabitant.
--
-- The timing observers internal/modules/definitions are alternative views:
-- only one is selected at a time.  Sharing/serialization/constraints/metas/
-- interactive/conversion are orthogonal diagnostic observers and may accompany
-- the selected timing view (e.g. --profile=all).
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.ComputerScience.AgdaElaborationResidencyComplexityExact as Residency

data AgdaTimingProfile : Set where
  internalTiming
  moduleTiming
  definitionTiming : AgdaTimingProfile

data AgdaCounterProfile : Set where
  sharingProfile
  serializationProfile
  constraintProfile
  metaProfile
  interactiveProfile
  conversionProfile : AgdaCounterProfile

record AgdaProfilerConfiguration : Set where
  constructor agdaProfilerConfiguration
  field
    timingView : AgdaTimingProfile
    observeSharing : Bool
    observeSerialization : Bool
    observeConstraints : Bool
    observeMetas : Bool
    observeInteractive : Bool
    observeConversion : Bool

open AgdaProfilerConfiguration public

-- Agda --profile=all selects internal timing together with the available
-- orthogonal profiler families.
profileAllConfiguration : AgdaProfilerConfiguration
profileAllConfiguration =
  agdaProfilerConfiguration
    internalTiming
    true true true true true true

-- Definition-local hotspot hunting uses the same orthogonal counters but swaps
-- the timing observer.  This is intentionally a separate profiling run/view.
definitionHotspotConfiguration : AgdaProfilerConfiguration
definitionHotspotConfiguration =
  agdaProfilerConfiguration
    definitionTiming
    true true true true false true

moduleConeTimingConfiguration : AgdaProfilerConfiguration
moduleConeTimingConfiguration =
  agdaProfilerConfiguration
    moduleTiming
    true true true true false true

------------------------------------------------------------------------
-- Typed profiler output.
------------------------------------------------------------------------

record AgdaProfilerCounts : Set where
  constructor agdaProfilerCounts
  field
    conversionEvents : Nat
    constraintEvents : Nat
    createdMetas : Nat
    sharingEvents : Nat
    serializationEvents : Nat

open AgdaProfilerCounts public

record AgdaProfilerTimingObservation : Set where
  constructor agdaProfilerTimingObservation
  field
    view : AgdaTimingProfile
    labelledEntries : Nat
    totalObservedTimeUnits : Nat

open AgdaProfilerTimingObservation public

record AgdaProfilerReceipt : Set where
  constructor agdaProfilerReceipt
  field
    configuration : AgdaProfilerConfiguration
    timing : AgdaProfilerTimingObservation
    counts : AgdaProfilerCounts
    runtimeResidency : Residency.ElaborationProfile

open AgdaProfilerReceipt public

------------------------------------------------------------------------
-- Epistemic firewall.
------------------------------------------------------------------------

record AgdaProfilerBoundary : Set where
  constructor agdaProfilerBoundary
  field
    profilerChangesTheoremSemantics : Bool
    profilerReceiptIsKernelProof : Bool
    timingViewsAreInterchangeable : Bool
    definitionTimingEqualsModuleTiming : Bool
    profileAllUsesDefinitionTimingByDefault : Bool
    runtimeResidencyIsSameAsConversionCount : Bool
    profilerCanDiagnoseElaborationShape : Bool
    profilerCanGuideRepairSelection : Bool

canonicalAgdaProfilerBoundary : AgdaProfilerBoundary
canonicalAgdaProfilerBoundary =
  agdaProfilerBoundary
    false false false false false false true true

------------------------------------------------------------------------
-- Cross-pollination with the existing residency classifier.
--
-- The profiler supplies observations; thresholds / qualitative labels remain
-- an explicit audit layer.  We deliberately do not pretend a raw counter alone
-- proves that a workload is conversion-heavy or residency-heavy.
------------------------------------------------------------------------

record ClassifiedAgdaProfilerReceipt : Set where
  constructor classifiedAgdaProfilerReceipt
  field
    receipt : AgdaProfilerReceipt
    classification : Residency.ElaborationObservation

open ClassifiedAgdaProfilerReceipt public

selectedRepair : ClassifiedAgdaProfilerReceipt → Residency.ElaborationIntervention
selectedRepair classified =
  Residency.selectIntervention (classification classified)

profilerDoesNotCollapseMachinePathCost : Bool
profilerDoesNotCollapseMachinePathCost = true

profileAllUsesInternalTiming :
  timingView profileAllConfiguration ≡ internalTiming
profileAllUsesInternalTiming = refl

definitionHotspotUsesDefinitionTiming :
  timingView definitionHotspotConfiguration ≡ definitionTiming
definitionHotspotUsesDefinitionTiming = refl
