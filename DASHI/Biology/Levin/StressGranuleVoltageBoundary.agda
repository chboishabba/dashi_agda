module DASHI.Biology.Levin.StressGranuleVoltageBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Stress-granule / membrane-potential boundary.
--
-- Both depolarising and hyperpolarising interventions may accompany granule
-- formation under different stresses.  Therefore granule formation cannot be
-- assigned a single voltage sign or a single molecular composition.

record StressGranuleContext : Set where
  field
    depolarised       : Bool
    hyperpolarised    : Bool
    ATPDepleted       : Bool
    granulesObserved  : Bool
    contextIndexed    : Bool

open StressGranuleContext public

record StressGranuleVoltageWitness : Set where
  field
    depolarisingContext : StressGranuleContext
    starvationContext   : StressGranuleContext

    depolarisationGranules :
      granulesObserved depolarisingContext ≡ true

    starvationGranules :
      granulesObserved starvationContext ≡ true

    oppositeVoltageSignsAllowed : Bool
    oppositeVoltageSignsAllowedIsTrue :
      oppositeVoltageSignsAllowed ≡ true

    granuleNotSingleStateMarker : Bool
    granuleNotSingleStateMarkerIsFalse :
      granuleNotSingleStateMarker ≡ false

    noClinicalInference : Bool
    noClinicalInferenceIsFalse : noClinicalInference ≡ false

    reading : String

open StressGranuleVoltageWitness public

canonicalDepolarisingContext : StressGranuleContext
canonicalDepolarisingContext = record
  { depolarised = true
  ; hyperpolarised = false
  ; ATPDepleted = false
  ; granulesObserved = true
  ; contextIndexed = true
  }

canonicalStarvationContext : StressGranuleContext
canonicalStarvationContext = record
  { depolarised = false
  ; hyperpolarised = true
  ; ATPDepleted = true
  ; granulesObserved = true
  ; contextIndexed = true
  }

canonicalStressGranuleVoltageWitness : StressGranuleVoltageWitness
canonicalStressGranuleVoltageWitness = record
  { depolarisingContext = canonicalDepolarisingContext
  ; starvationContext = canonicalStarvationContext
  ; depolarisationGranules = refl
  ; starvationGranules = refl
  ; oppositeVoltageSignsAllowed = true
  ; oppositeVoltageSignsAllowedIsTrue = refl
  ; granuleNotSingleStateMarker = false
  ; granuleNotSingleStateMarkerIsFalse = refl
  ; noClinicalInference = false
  ; noClinicalInferenceIsFalse = refl
  ; reading =
      "Stress-granule formation is voltage- and stress-context indexed; neither granule presence nor voltage sign alone determines a unique biological state"
  }
