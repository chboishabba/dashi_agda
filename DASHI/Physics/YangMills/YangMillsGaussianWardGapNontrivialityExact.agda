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
-- `YangMillsGaussianWardTwoDerivativeMaxwellClassificationExact` proves the
-- nontrivial coefficient step: a local O(4)-covariant two-derivative Gaussian
-- kernel satisfying the exact Ward identity at two nonzero momentum squares
-- and the standard kinetic normalization is exactly Maxwell:
--
--     m^2 = 0,  Z = 1,  Y = -1.
--
-- `YangMillsMaxwellLinearDispersionNoGapExact` then compiles the standard
-- massless transverse one-particle dispersion into the existing no-gap
-- contradiction.
--
-- This module performs the SAME-SYSTEM assembly. The Gaussian predicate is on
-- the actual continuum Schwinger system; the positive-gap input is on the
-- Hamiltonian reconstructed from that same system. Thus nontriviality can be
-- downstream of the continuum Ward/locality theorem plus the clustering/gap
-- theorem rather than an independent fourth-cumulant estimate.
------------------------------------------------------------------------

open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YangMillsFreeGaussianMaxwellNoGapExact as Free
import DASHI.Physics.YangMills.YangMillsMaxwellLinearDispersionNoGapExact as Disp
import DASHI.Physics.YangMills.YangMillsGaussianWardTwoDerivativeMaxwellClassificationExact as Ward

------------------------------------------------------------------------
-- Same-family authority package.
--
-- The only standard imported step is the free/Gaussian OS statement: once the
-- SAME system has the Maxwell quadratic kernel, its reconstructed one-particle
-- sector is the massless Maxwell sector. Everything else is exact assembly.
------------------------------------------------------------------------

record SameSystemGaussianWardGapData
    {Observable Point Scalar : Set}
    (system : OS.ContinuumSchwingerSystem Observable Point Scalar) : Set₂ where
  field
    reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system

    Gaussian : OS.ContinuumSchwingerSystem Observable Point Scalar → Set

    -- Supplied by the strengthened same-family local/OPE/stress/Ward theorem.
    localWardKernelUnderGaussian :
      Gaussian system → Ward.LocalTwoDerivativeWardKernel

    -- Spectral order used by the reconstructed Hamiltonian.
    gapOrder : Free.GapOrder

    -- Standard Gaussian OS/Fock reconstruction after the exact coefficient
    -- classification has identified the kernel as Maxwell.
    gaussianMaxwellDispersion :
      (gaussian : Gaussian system) →
      Ward.MaxwellQuadraticKernelClassification
        (localWardKernelUnderGaussian gaussian) →
      Disp.LabelledLinearMasslessDispersion gapOrder

    -- The physical gap is a theorem about the SAME reconstructed Hamiltonian.
    PhysicalPositiveGap : OS.Hamiltonian reconstruction → Set
    physicalPositiveGap :
      PhysicalPositiveGap (OS.hamiltonian reconstruction)

    gapRestrictsToSameMaxwellSector :
      (gaussian : Gaussian system) →
      (classification : Ward.MaxwellQuadraticKernelClassification
        (localWardKernelUnderGaussian gaussian)) →
      PhysicalPositiveGap (OS.hamiltonian reconstruction) →
      Free.PositiveSpectralGap
        (Disp.labelledLinearDispersionGivesMasslessSector
          (gaussianMaxwellDispersion gaussian classification))

    -- A positive gap says precisely that the below-gap/non-vacuum witness is
    -- impossible; expose that contradiction as bottom for this same H.
    spectralGapContradictionIsAbsurd :
      (gaussian : Gaussian system) →
      (classification : Ward.MaxwellQuadraticKernelClassification
        (localWardKernelUnderGaussian gaussian)) →
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
    kernel = localWardKernelUnderGaussian dataSet gaussian
    classification = Ward.classifyLocalWardKernelAsMaxwell kernel
    dispersion = gaussianMaxwellDispersion dataSet gaussian classification
    gapData = gapRestrictsToSameMaxwellSector dataSet
      gaussian classification (physicalPositiveGap dataSet)
    contradiction =
      Disp.labelledLinearDispersionContradictsPositiveGap dispersion gapData
  in
  spectralGapContradictionIsAbsurd dataSet
    gaussian classification contradiction

------------------------------------------------------------------------
-- Existing Clay-facing interacting witness can therefore be instantiated by
-- literal non-Gaussianity of the SAME continuum Schwinger system.
------------------------------------------------------------------------

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

-- Standard free/Gaussian reconstruction, once the exact Schwinger covariance
-- has been identified with Maxwell, is imported constructive-QFT machinery.
gaussianOSMaxwellOneParticleReconstructionLevel : ProofLevel
gaussianOSMaxwellOneParticleReconstructionLevel = standardImported

-- The genuinely physical inputs have now moved into the two existing jobs:
--   * localWardKernelUnderGaussian belongs to SameFamilyCompositeOPEStressWard;
--   * physicalPositiveGap belongs to SameDensity...Clustering.
-- There is no separate continuum cumulant estimate on this route.
