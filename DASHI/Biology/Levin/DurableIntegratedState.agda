module DASHI.Biology.Levin.DurableIntegratedState where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.FunctionalAgencyRatchet as Ratchet
import DASHI.Biology.Levin.BoundaryHiddenStateNonrecurrence as Hidden
import DASHI.Biology.Levin.OscillatoryMemoryStorageAdapter as Memory

record IntegrationTrajectory : Set where
  field
    integrationMeasuredDuringInput : Bool
    integrationMeasuredAfterInput  : Bool
    latentStateProbedAfterQuiescence : Bool
    reactivationGainMeasured       : Bool
    decayTimescaleMeasured         : Bool
    perturbationSpecificityMeasured : Bool

record DurableIntegratedStateBoundary : Set where
  field
    ratchetBoundary : Ratchet.RatchetInterpretationBoundary
    hiddenStateType : Set
    memoryAdapterType : Set
    transientIntegrationNotPersistentSelf : Bool
    returnToBaselineNotErasure : Bool
    reactivationGainRequiresStoredStateModel : Bool
    durabilityNotConsciousness : Bool
    memoryNecessaryForConsciousnessNotProven : Bool
    causalEmergenceMetricNotUnique : Bool
    interpretation : String

canonicalDurableIntegratedStateBoundary : DurableIntegratedStateBoundary
canonicalDurableIntegratedStateBoundary = record
  { ratchetBoundary = Ratchet.canonicalRatchetInterpretationBoundary
  ; hiddenStateType = Hidden.HiddenStateNonrecurrenceBoundary
  ; memoryAdapterType = Memory.OscillatoryMemoryStorageAdapter
  ; transientIntegrationNotPersistentSelf = true
  ; returnToBaselineNotErasure = true
  ; reactivationGainRequiresStoredStateModel = true
  ; durabilityNotConsciousness = true
  ; memoryNecessaryForConsciousnessNotProven = true
  ; causalEmergenceMetricNotUnique = true
  ; interpretation = "Integration, persistence, quiescent latent state and reactivation gain are separate measurements; durable state is a candidate prerequisite for some forms of agency but is not consciousness by definition"
  }
