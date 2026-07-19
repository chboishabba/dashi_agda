module DASHI.Biology.Levin.FungalMemoryInterventionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.DurableIntegratedState as Durable
import DASHI.Biology.Levin.BoundaryHiddenStateNonrecurrence as Hidden
import DASHI.Biology.Levin.FungalNetworkAgencyBoundary as Fungal

record FungalMemoryProtocol : Set where
  field
    exposureSpecified : Bool
    matchedUnexposedControl : Bool
    stimulusRemoved : Bool
    quiescentIntervalSpecified : Bool
    persistentStateDifferenceMeasured : Bool
    laterResponseAltered : Bool
    morphologySeparatedFromPhysiology : Bool
    environmentalTraceExcluded : Bool
    perturbationOfStoredStateAttempted : Bool
    replicationAcrossColonies : Bool

record FungalMemoryInterventionBoundary : Set where
  field
    fungalBoundary : Fungal.FungalNetworkAgencyBoundary
    durableStateBoundary : Durable.DurableIntegratedStateBoundary
    hiddenStateBoundary : Hidden.NonrecurrenceBoundary
    historyDependenceNotMemoryByDefinition : Bool
    persistentMorphologyMayCarryState : Bool
    persistentPhysiologyMayCarryState : Bool
    epigeneticCarrierAdmissible : Bool
    externalEnvironmentalTraceAdmissible : Bool
    returnToBaselineNotErasure : Bool
    memoryNotConsciousness : Bool
    interpretation : String

canonicalFungalMemoryInterventionBoundary : FungalMemoryInterventionBoundary
canonicalFungalMemoryInterventionBoundary = record
  { fungalBoundary = Fungal.canonicalFungalNetworkAgencyBoundary
  ; durableStateBoundary = Durable.canonicalDurableIntegratedStateBoundary
  ; hiddenStateBoundary = Hidden.canonicalNonrecurrenceBoundary
  ; historyDependenceNotMemoryByDefinition = true
  ; persistentMorphologyMayCarryState = true
  ; persistentPhysiologyMayCarryState = true
  ; epigeneticCarrierAdmissible = true
  ; externalEnvironmentalTraceAdmissible = true
  ; returnToBaselineNotErasure = true
  ; memoryNotConsciousness = true
  ; interpretation = "A fungal memory claim requires exposure, stimulus removal, persistence through a specified interval, altered later response, matched controls and discrimination among morphological, physiological, epigenetic and environmental carriers"
  }
