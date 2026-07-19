module DASHI.Biology.Levin.PolycomputationBiologyAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.LevinBioelectricAgencyCore as Levin
import DASHI.Biology.Levin.ExistingBiologyPhysicalStateAdapter as Existing

record PhysicalComputationInterpretation : Set where
  field
    observedBehaviourIsProjection : Bool
    multipleAbstractComputationsMayFitOneBehaviour : Bool
    thermodynamicSideProcessesRemainUnobserved : Bool
    interpretationRequiresChosenEncoding : Bool

record PolycomputationBiologyAdapter : Set where
  field
    levinAgencyCore : Levin.LevinBioelectricAgencyCore
    existingBiologyAdapter : Existing.ExistingBiologyPhysicalStateAdapter
    computationInterpretation : PhysicalComputationInterpretation
    projectionIsNotUniqueMechanism : Bool
    polycomputationDoesNotImplyUnlimitedIntelligence : Bool
    physicalImplementationDoesNotImplyConsciousness : Bool
    interpretation : String

canonicalPhysicalComputationInterpretation : PhysicalComputationInterpretation
canonicalPhysicalComputationInterpretation = record
  { observedBehaviourIsProjection = true
  ; multipleAbstractComputationsMayFitOneBehaviour = true
  ; thermodynamicSideProcessesRemainUnobserved = true
  ; interpretationRequiresChosenEncoding = true
  }

canonicalPolycomputationBiologyAdapter : PolycomputationBiologyAdapter
canonicalPolycomputationBiologyAdapter = record
  { levinAgencyCore = Levin.canonicalLevinBioelectricAgencyCore
  ; existingBiologyAdapter = Existing.canonicalExistingBiologyPhysicalStateAdapter
  ; computationInterpretation = canonicalPhysicalComputationInterpretation
  ; projectionIsNotUniqueMechanism = true
  ; polycomputationDoesNotImplyUnlimitedIntelligence = true
  ; physicalImplementationDoesNotImplyConsciousness = true
  ; interpretation = "Existing biology and Levin agency surfaces are read through an explicitly chosen computation projection; observable behaviour underdetermines mechanism"
  }
