module DASHI.Physics.YangMills.YangMillsGaussianWardGapNontrivialityExact where

------------------------------------------------------------------------
-- ROUND77: GAUSSIAN + SAME-FAMILY WARD/MAXWELL + POSITIVE GAP -> NON-GAUSSIAN
--
-- PRIMARY / CALIBRATION SOURCES
--
-- James Glimm and Arthur Jaffe,
-- "Quantum Physics: A Functional Integral Point of View", 2nd ed., Springer,
-- 1987. DOI: 10.1007/978-1-4612-4728-9.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions", Communications in Mathematical
-- Physics 31 (1973), 83--112. DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II", Communications in
-- Mathematical Physics 42 (1975), 281--305. DOI: 10.1007/BF01608978.
--
-- E. Huguet and J. Renaud,
-- "Two-point function for the Maxwell field in flat Robertson-Walker
-- spacetimes", Physical Review D 88 (2013), 124018.
-- DOI: 10.1103/PhysRevD.88.124018.
--
-- DASHI CONTRIBUTION
--
-- The Ward->Maxwell coefficient theorem is generic over the continuum scalar
-- additive group; it does not assume rational coefficients. This module then
-- performs the SAME-SYSTEM assembly. The Gaussian predicate is on the actual
-- continuum Schwinger system and the positive-gap input is on the Hamiltonian
-- reconstructed from that same system.
------------------------------------------------------------------------

open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YangMillsFreeGaussianMaxwellNoGapExact as Free
import DASHI.Physics.YangMills.YangMillsMaxwellLinearDispersionNoGapExact as Disp
import DASHI.Physics.YangMills.YangMillsGaussianWardTwoDerivativeMaxwellClassificationExact as Ward

record SameSystemGaussianWardGapData
    {Observable Point Scalar : Set}
    (system : OS.ContinuumSchwingerSystem Observable Point Scalar) : Set₂ where
  field
    reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system

    Gaussian : OS.ContinuumSchwingerSystem Observable Point Scalar → Set

    coefficientAlgebra : Ward.WardCoefficientAdditiveGroup

    -- Supplied by strengthened same-family local/OPE/stress/Ward job #5.
    localWardKernelUnderGaussian :
      Gaussian system →
      Ward.GenericLocalTwoDerivativeWardKernel coefficientAlgebra

    gapOrder : Free.GapOrder

    -- Standard Gaussian OS/Fock reconstruction after exact coefficient
    -- classification has identified the quadratic kernel as Maxwell.
    gaussianMaxwellDispersion :
      (gaussian : Gaussian system) →
      Ward.GenericMaxwellQuadraticKernelClassification
        coefficientAlgebra (localWardKernelUnderGaussian gaussian) →
      Disp.LabelledLinearMasslessDispersion gapOrder

    -- Physical gap from job #4, on the SAME reconstructed Hamiltonian.
    PhysicalPositiveGap : OS.Hamiltonian reconstruction → Set
    physicalPositiveGap :
      PhysicalPositiveGap (OS.hamiltonian reconstruction)

    -- Standard spectral restriction to the SAME Maxwell one-particle sector.
    gapRestrictsToSameMaxwellSector :
      (gaussian : Gaussian system) →
      (classification : Ward.GenericMaxwellQuadraticKernelClassification
        coefficientAlgebra (localWardKernelUnderGaussian gaussian)) →
      PhysicalPositiveGap (OS.hamiltonian reconstruction) →
      Free.PositiveSpectralGap
        (Disp.labelledLinearDispersionGivesMasslessSector
          (gaussianMaxwellDispersion gaussian classification))

    spectralGapContradictionIsAbsurd :
      (gaussian : Gaussian system) →
      (classification : Ward.GenericMaxwellQuadraticKernelClassification
        coefficientAlgebra (localWardKernelUnderGaussian gaussian)) →
      let dispersion = gaussianMaxwellDispersion gaussian classification
          gapData = gapRestrictsToSameMaxwellSector
            gaussian classification physicalPositiveGap
      in
      Free.SpectralContradiction gapData → ⊥

open SameSystemGaussianWardGapData public

gaussianSameSystemContradiction :
  ∀ {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar} →
  (dataSet : SameSystemGaussianWardGapData system) →
  Gaussian dataSet system → ⊥
gaussianSameSystemContradiction dataSet gaussian =
  let
    algebra = coefficientAlgebra dataSet
    kernel = localWardKernelUnderGaussian dataSet gaussian
    classification =
      Ward.classifyGenericLocalWardKernelAsMaxwell algebra kernel
    dispersion = gaussianMaxwellDispersion dataSet gaussian classification
    gapData = gapRestrictsToSameMaxwellSector dataSet
      gaussian classification (physicalPositiveGap dataSet)
    contradiction =
      Disp.labelledLinearDispersionContradictsPositiveGap dispersion gapData
  in
  spectralGapContradictionIsAbsurd dataSet
    gaussian classification contradiction

nonGaussianityGivesInteractingContinuumWitness :
  ∀ {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar} →
  (dataSet : SameSystemGaussianWardGapData system) →
  OS.InteractingContinuumWitness Observable Point Scalar system
nonGaussianityGivesInteractingContinuumWitness {system = system} dataSet = record
  { OS.InteractingContinuumWitness.Witness = Gaussian dataSet system → ⊥
  ; OS.InteractingContinuumWitness.witness =
      gaussianSameSystemContradiction dataSet
  }

wardMaxwellCoefficientCompilerLevel : ProofLevel
wardMaxwellCoefficientCompilerLevel = machineChecked

gaussianGapNontrivialityCompilerLevel : ProofLevel
gaussianGapNontrivialityCompilerLevel = machineChecked

gaussianOSMaxwellOneParticleReconstructionLevel : ProofLevel
gaussianOSMaxwellOneParticleReconstructionLevel = standardImported

-- Remaining physical inputs are assigned to existing jobs #4/#5; no separate
-- continuum cumulant estimate is present on this route.
