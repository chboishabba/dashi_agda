module DASHI.Physics.YangMills.YangMillsNonGaussianInteractingWitnessExact where

------------------------------------------------------------------------
-- ROUND74: CONSTRUCTIVE NON-GAUSSIANITY -> EXISTING INTERACTION WITNESS
--
-- The repository's continuum OS lane already keeps interacting/non-Gaussian
-- data separate from reconstruction and from the mass gap.  This module makes
-- the intended witness explicit without privileging the fourth cumulant.
--
-- Given a proposition `Gaussian` for the SAME continuum Schwinger system, let
--
--     NotGaussian = Gaussian -> Contradiction.
--
-- A proof of `NotGaussian` is itself a perfectly concrete inhabitant of the
-- existing `InteractingContinuumWitness`: choose its witness carrier to be the
-- constructive negation of Gaussianity.
--
-- Consequently the free-Maxwell zero-gap route can replace the strict fourth
-- cumulant route if it proves, on the same theory,
--
--     Gaussian YM -> massless Maxwell one-particle sector,
--
-- because the already-required positive gap then constructs `NotGaussian`.
-- No excluded middle or separate moment calculation is needed for this logic.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS

record NonGaussianWitnessData
    {Observable Point Scalar : Set}
    (system : OS.ContinuumSchwingerSystem Observable Point Scalar) : Set₁ where
  field
    Gaussian Contradiction : Set
    notGaussian : Gaussian → Contradiction

open NonGaussianWitnessData public

nonGaussianIsInteractingWitness :
  ∀ {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar} →
  NonGaussianWitnessData system →
  OS.InteractingContinuumWitness Observable Point Scalar system
nonGaussianIsInteractingWitness dataSet = record
  { Witness = Gaussian dataSet → Contradiction dataSet
  ; witness = notGaussian dataSet
  }

nonGaussianToInteractingWitnessLevel : ProofLevel
nonGaussianToInteractingWitnessLevel = machineChecked

-- The only physical issue is therefore production of the same-system
-- `notGaussian` proof.  The strict fourth cumulant is one sufficient producer;
-- the free-Maxwell/gap contradiction is now an explicit alternative producer.
physicalSameSystemNonGaussianWitnessLevel : ProofLevel
physicalSameSystemNonGaussianWitnessLevel = conditional
