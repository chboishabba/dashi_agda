module DASHI.Physics.QuantumVacuum.GroundStateSuppressionConjecture where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.QuantumVacuum.ExtractionPhysicsSurface as Surface

------------------------------------------------------------------------
-- The physically useful conjecture is kept separate from the much stronger
-- claim of net vacuum-energy extraction.
------------------------------------------------------------------------

record CavityGroundStateExperiment : Set where
  constructor mkCavityGroundStateExperiment
  field
    freeGroundEnergy      : Nat
    cavityGroundEnergy    : Nat
    measuredReleasedEnergy : Nat

    cavityModeSuppressionObserved : Bool
    stateShiftObserved            : Bool
    calorimetricReleaseObserved   : Bool

    chemistryExcluded       : Bool
    wallHeatingExcluded     : Bool
    contaminationExcluded   : Bool
    ordinaryCavityQEDExcluded : Bool
    replicated              : Bool

record GroundStateShiftWitness (e : CavityGroundStateExperiment) : Set where
  constructor mkGroundStateShiftWitness
  field
    modeSuppressionClosed :
      CavityGroundStateExperiment.cavityModeSuppressionObserved e ≡ true
    stateShiftClosed :
      CavityGroundStateExperiment.stateShiftObserved e ≡ true

record VacuumExtractionDiscrimination (e : CavityGroundStateExperiment) : Set where
  constructor mkVacuumExtractionDiscrimination
  field
    calorimetryClosed :
      CavityGroundStateExperiment.calorimetricReleaseObserved e ≡ true
    chemistryClosed :
      CavityGroundStateExperiment.chemistryExcluded e ≡ true
    wallHeatingClosed :
      CavityGroundStateExperiment.wallHeatingExcluded e ≡ true
    contaminationClosed :
      CavityGroundStateExperiment.contaminationExcluded e ≡ true
    ordinaryCavityQEDClosed :
      CavityGroundStateExperiment.ordinaryCavityQEDExcluded e ≡ true
    replicationClosed :
      CavityGroundStateExperiment.replicated e ≡ true

-- A measured cavity-induced state shift is already useful physics, even when
-- extraction is not established.

stateShiftIsWeakerThanExtraction :
  (e : CavityGroundStateExperiment) → GroundStateShiftWitness e →
  Surface.ExtractionClaim
stateShiftIsWeakerThanExtraction e shift =
  Surface.mkExtractionClaim
    Surface.groundStateSuppression
    Surface.transient
    Surface.preliminaryExperiment
    true true false false false

stateShiftAloneNotPromoted :
  (e : CavityGroundStateExperiment) → (shift : GroundStateShiftWitness e) →
  Surface.promotable? (stateShiftIsWeakerThanExtraction e shift) ≡ false
stateShiftAloneNotPromoted e shift = refl

-- Only the conjunction of state-shift evidence and discriminating controls
-- can populate the extraction-facing promotion witness.

controlledExperimentToClaim :
  (e : CavityGroundStateExperiment) →
  GroundStateShiftWitness e →
  VacuumExtractionDiscrimination e →
  Surface.ExtractionClaim
controlledExperimentToClaim e shift controls =
  Surface.mkExtractionClaim
    Surface.groundStateSuppression
    Surface.transient
    Surface.replicatedExperiment
    true true true true true

controlledExperimentPromotes :
  (e : CavityGroundStateExperiment) →
  (shift : GroundStateShiftWitness e) →
  (controls : VacuumExtractionDiscrimination e) →
  Surface.promotable? (controlledExperimentToClaim e shift controls) ≡ true
controlledExperimentPromotes e shift controls = refl
