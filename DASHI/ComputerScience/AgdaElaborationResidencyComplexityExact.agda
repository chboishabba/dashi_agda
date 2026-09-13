{-# OPTIONS --safe #-}
module DASHI.ComputerScience.AgdaElaborationResidencyComplexityExact where

------------------------------------------------------------------------
-- AGDA ELABORATION RESIDENCY / CS PATH-COMPLEXITY SEPARATION
--
-- Cross-pollination from FibreProgramComplexityExact:
--
--   K_C(gamma) is a consumer-indexed cost of an abstract machine path.
--   Agda elaboration cost is a different consumer over the proof/checker run.
--
-- A nontrivial program can have loops, branches, head travel and representation
-- fibres while remaining a cheap elaboration workload.  Conversely, one large
-- dependent conversion/equality can dominate memory without a large abstract
-- execution path.  The two coordinates must therefore never be collapsed.
--
-- Runtime profiler measurements are empirical receipts.  This module does not
-- manufacture them or promote them to kernel facts about GHC/Agda performance.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.ComputerScience.FibreProgramComplexityExact as Path

record ElaborationProfile : Set where
  constructor elaborationProfile
  field
    allocatedBytes : Nat
    maximumResidencyBytes : Nat
    maximumRSSKiB : Nat
    conversionActivity : Nat
    constraintActivity : Nat
    createdMetas : Nat
    sharingActivity : Nat
    gcCost : Nat

open ElaborationProfile public

record ElaborationObservation : Set where
  constructor elaborationObservation
  field
    metrics : ElaborationProfile

    -- These are observer judgements produced by the profiling/audit layer.
    -- They are intentionally explicit rather than inferred from arbitrary
    -- numeric thresholds inside the formal core.
    residencyHeavy : Bool
    conversionHeavy : Bool
    constraintOrMetaHeavy : Bool
    repeatedNormalizationOrPoorSharing : Bool
    importedStateHeavy : Bool

open ElaborationObservation public

data ElaborationIntervention : Set where
  stageEqualityOrConversion
  exposeIndicesAndSplitInference
  nameAndShareIntermediateTerms
  performInterfaceConeSurgery
  noElaborationSurgerySelected : ElaborationIntervention

selectIntervention : ElaborationObservation -> ElaborationIntervention
selectIntervention observation with residencyHeavy observation | conversionHeavy observation
... | true | true = stageEqualityOrConversion
... | true | false with constraintOrMetaHeavy observation
...   | true = exposeIndicesAndSplitInference
...   | false with repeatedNormalizationOrPoorSharing observation
...     | true = nameAndShareIntermediateTerms
...     | false with importedStateHeavy observation
...       | true = performInterfaceConeSurgery
...       | false = noElaborationSurgerySelected
... | false | _ with repeatedNormalizationOrPoorSharing observation
...   | true = nameAndShareIntermediateTerms
...   | false with importedStateHeavy observation
...     | true = performInterfaceConeSurgery
...     | false = noElaborationSurgerySelected

------------------------------------------------------------------------
-- Non-collapse boundary.
------------------------------------------------------------------------

record PathElaborationBoundary : Set where
  constructor pathElaborationBoundary
  field
    machineTransitionCountIsElaborationResidency : Bool
    machineHeadTravelIsElaborationResidency : Bool
    representationCellCountIsElaborationResidency : Bool
    sourceNestednessAlonePredictsOOM : Bool
    importCountAlonePredictsOOM : Bool
    moduleParallelismIsPrimarySingleModuleCause : Bool
    allocationEqualsLiveResidency : Bool
    liveResidencyEqualsRSS : Bool
    elaborationCostNeedsOwnConsumer : Bool
    runtimeMeasurementsRemainEmpiricalReceipts : Bool

canonicalPathElaborationBoundary : PathElaborationBoundary
canonicalPathElaborationBoundary =
  pathElaborationBoundary
    false false false
    false false false
    false false
    true true

------------------------------------------------------------------------
-- The CS path owner is reused as the semantic witness that execution costs are
-- already independently consumer-indexed.  We do not reinterpret those costs
-- as checker costs.
------------------------------------------------------------------------

executionPathComplexityRemainsConsumerIndexed : Bool
executionPathComplexityRemainsConsumerIndexed =
  Path.FibreComplexityBoundary.complexityCanBePathIndexed
    Path.canonicalFibreComplexityBoundary

headTravelRemainsIndependentCoordinate : Bool
headTravelRemainsIndependentCoordinate =
  Path.FibreComplexityBoundary.headPathIsAComplexityCoordinate
    Path.canonicalFibreComplexityBoundary

pathCostDoesNotSelectElaborationIntervention : Bool
pathCostDoesNotSelectElaborationIntervention = true
