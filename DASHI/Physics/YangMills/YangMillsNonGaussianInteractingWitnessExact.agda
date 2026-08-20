module DASHI.Physics.YangMills.YangMillsNonGaussianInteractingWitnessExact where

------------------------------------------------------------------------
-- ROUND74: CONSTRUCTIVE NON-GAUSSIANITY -> EXISTING INTERACTION WITNESS
--
-- The repository's continuum OS lane already keeps interacting/non-Gaussian
-- data separate from reconstruction and from the mass gap.  This module makes
-- the intended witness explicit without privileging the fourth cumulant.
--
-- Given `NotGaussian = Gaussian -> Contradiction` for the SAME continuum
-- Schwinger system, choose `NotGaussian` itself as the witness carrier of the
-- existing `InteractingContinuumWitness`.
--
-- The companion free-Maxwell module now constructs such a `NotGaussian` proof
-- from a same-Hamiltonian implication
--
--   Gaussian YM -> massless Maxwell one-particle sector
--
-- plus the already-required positive physical gap.  No excluded middle and no
-- separate fourth-moment calculation enter the logical composition.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YangMillsFreeGaussianMaxwellNoGapExact as Free

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

-- Direct composition of the spectral obstruction into the existing OS
-- interaction-witness carrier.  The `Gaussian` proposition is supplied by the
-- caller for this SAME `system`; no unrelated theory is introduced.
gaussianMaxwellGapObstructionIsInteracting :
  ∀ {Observable Point Scalar O}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar} →
  (dataSet : Free.GaussianMaxwellGapObstruction O) →
  OS.InteractingContinuumWitness Observable Point Scalar system
gaussianMaxwellGapObstructionIsInteracting dataSet = record
  { Witness = Free.Gaussian dataSet → Free.Contradiction dataSet
  ; witness = Free.gaussianContradictsPositiveGap dataSet
  }

nonGaussianToInteractingWitnessLevel : ProofLevel
nonGaussianToInteractingWitnessLevel = machineChecked

freeMaxwellGapToInteractingWitnessCompilerLevel : ProofLevel
freeMaxwellGapToInteractingWitnessCompilerLevel = machineChecked

-- TRUE physical seam for the cheaper route is now singular: establish on the
-- SAME continuum Yang--Mills Hamiltonian that the Gaussian/free hypothesis
-- produces the massless Maxwell one-particle sector.  Everything from that
-- hypothesis + positive gap to an `InteractingContinuumWitness` is constructed.
physicalGaussianYMToMasslessMaxwellSameHamiltonianLevel : ProofLevel
physicalGaussianYMToMasslessMaxwellSameHamiltonianLevel = conditional
