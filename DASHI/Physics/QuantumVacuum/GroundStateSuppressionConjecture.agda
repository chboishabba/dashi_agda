module DASHI.Physics.QuantumVacuum.GroundStateSuppressionConjecture where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.QuantumVacuum.ExtractionPhysicsSurface as Surface
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q
import DASHI.Physics.QuantumVacuum.ReservoirDynamics as Reservoir

------------------------------------------------------------------------
-- The physically useful conjecture is staged.  A replicated cavity-induced
-- state shift and anomalous calorimetric release do not yet identify the
-- source as vacuum energy, establish reabsorption on exit, or close a cycle.
------------------------------------------------------------------------

record CavityGroundStateExperiment : Set where
  constructor mkCavityGroundStateExperiment
  field
    freeGroundEnergy       : Q.Energy
    cavityGroundEnergy     : Q.Energy
    measuredReleasedEnergy : Q.Energy

    cavityModeSuppressionObserved : Bool
    stateShiftObserved            : Bool
    calorimetricReleaseObserved   : Bool

    chemistryExcluded        : Bool
    wallHeatingExcluded      : Bool
    contaminationExcluded    : Bool
    ordinaryCavityQEDExcluded : Bool
    replicated               : Bool

record GroundStateShiftWitness (e : CavityGroundStateExperiment) : Set where
  constructor mkGroundStateShiftWitness
  field
    modeSuppressionClosed :
      CavityGroundStateExperiment.cavityModeSuppressionObserved e ≡ true
    stateShiftClosed :
      CavityGroundStateExperiment.stateShiftObserved e ≡ true

record AnomalousEnergyReleaseWitness (e : CavityGroundStateExperiment) : Set where
  constructor mkAnomalousEnergyReleaseWitness
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

record VacuumSourceDiscrimination (e : CavityGroundStateExperiment) : Set₁ where
  constructor mkVacuumSourceDiscrimination
  field
    anomalousRelease : AnomalousEnergyReleaseWitness e
    vacuumSpecificPrediction : Set
    competingReservoirsExcluded : Set

record ResetReabsorptionEstablished (e : CavityGroundStateExperiment) : Set₁ where
  constructor mkResetReabsorptionEstablished
  field
    sourceDiscrimination : VacuumSourceDiscrimination e
    exitStateRestored : Set
    restorationEnergySourceIdentified : Set
    noExternalResetEnergy : Set

record ContinuousGroundStateClosure (e : CavityGroundStateExperiment) : Set₁ where
  constructor mkContinuousGroundStateClosure
  field
    resetEstablished : ResetReabsorptionEstablished e
    reservoir : Reservoir.ReservoirDynamics
    reservoirClosure : Reservoir.ContinuousReservoirClosure reservoir

stateShiftClaim :
  (e : CavityGroundStateExperiment) → GroundStateShiftWitness e →
  Surface.ExtractionClaim
stateShiftClaim e shift =
  Surface.mkExtractionClaim
    Surface.groundStateSuppression
    Surface.transient
    Surface.preliminaryExperiment
    true true false false false

stateShiftAloneNotPromoted :
  (e : CavityGroundStateExperiment) → (shift : GroundStateShiftWitness e) →
  Surface.promotable? (stateShiftClaim e shift) ≡ false
stateShiftAloneNotPromoted e shift = refl

anomalousReleaseClaim :
  (e : CavityGroundStateExperiment) →
  GroundStateShiftWitness e →
  AnomalousEnergyReleaseWitness e →
  Surface.ExtractionClaim
anomalousReleaseClaim e shift anomaly =
  Surface.mkExtractionClaim
    Surface.groundStateSuppression
    Surface.transient
    Surface.replicatedExperiment
    true true true false true

anomalousReleaseStillNeedsReset :
  (e : CavityGroundStateExperiment) →
  (shift : GroundStateShiftWitness e) →
  (anomaly : AnomalousEnergyReleaseWitness e) →
  Surface.promotable? (anomalousReleaseClaim e shift anomaly) ≡ false
anomalousReleaseStillNeedsReset e shift anomaly = refl

continuousClosureClaim :
  (e : CavityGroundStateExperiment) →
  GroundStateShiftWitness e →
  ContinuousGroundStateClosure e →
  Surface.ExtractionClaim
continuousClosureClaim e shift closure =
  Surface.mkExtractionClaim
    Surface.groundStateSuppression
    Surface.continuous
    Surface.closedEngineeringCycle
    true true true true true

continuousGroundStateClosurePromotes :
  (e : CavityGroundStateExperiment) →
  (shift : GroundStateShiftWitness e) →
  (closure : ContinuousGroundStateClosure e) →
  Surface.promotable? (continuousClosureClaim e shift closure) ≡ true
continuousGroundStateClosurePromotes e shift closure = refl
