module DASHI.Biology.Levin.AnesthesiaPhaseFragmentation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record CorticalPhaseState
  (Region Frequency Phase Coupling : Set) : Set where
  field
    dominantFrequency : Region → Frequency
    phaseAt : Region → Phase
    couplingBetween : Region → Region → Coupling
    localSpikePhaseLocking : Bool
    longRangePhaseAlignment : Bool

record AnesthesiaTransitionWitness
  {Region Frequency Phase Coupling : Set}
  (awake anesthetized : CorticalPhaseState Region Frequency Phase Coupling) : Set where
  field
    frequencyShiftedLower : Bool
    localPhaseLockingRetained : Bool
    longRangeAlignmentReduced : Bool
    corticalCommunicationFragmented : Bool

record CrossDrugConvergenceWitness : Set where
  field
    molecularTargetsDiffer : Bool
    fieldLevelSignatureConverges : Bool
    behaviouralUnresponsivenessConverges : Bool
    replicatedAcrossSubjectsAndDrugs : Bool

record AnesthesiaClaimBoundary : Set where
  field
    commonWaveSignatureDoesNotProveUniqueCause : Bool
    unresponsivenessDoesNotEqualAbsenceOfAllExperience : Bool
    phaseFragmentationRequiresQuantitativeCriterion : Bool
    molecularAndFieldDescriptionsAreNotCompetitorsByDefinition : Bool

canonicalAnesthesiaClaimBoundary : AnesthesiaClaimBoundary
canonicalAnesthesiaClaimBoundary = record
  { commonWaveSignatureDoesNotProveUniqueCause = true
  ; unresponsivenessDoesNotEqualAbsenceOfAllExperience = true
  ; phaseFragmentationRequiresQuantitativeCriterion = true
  ; molecularAndFieldDescriptionsAreNotCompetitorsByDefinition = true
  }
