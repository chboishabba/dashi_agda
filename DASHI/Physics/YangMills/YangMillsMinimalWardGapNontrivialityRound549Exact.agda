{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsMinimalWardGapNontrivialityRound549Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND549:
-- MINIMAL SAME-SYSTEM NONTRIVIALITY PACKAGE
--
-- The Gaussian reductio does NOT require the full local OPE/stress package.
-- It consumes only:
--
--   * the SAME continuum Schwinger system;
--   * a Gaussian predicate on that system;
--   * the local two-derivative Ward kernel under that Gaussian hypothesis;
--   * the standard gauge-invariant Maxwell/Fock reconstruction;
--   * a positive gap on the SAME reconstructed Hamiltonian/physical sector.
--
-- Full OPE/stress/curvature machinery remains part of conservative Clay local
-- QFT completion, but it is no longer a prerequisite of the shortest H6
-- nontriviality argument.
------------------------------------------------------------------------

open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YangMillsFreeGaussianMaxwellNoGapExact as Free
import DASHI.Physics.YangMills.YangMillsMaxwellLinearDispersionNoGapExact as Disp
import DASHI.Physics.YangMills.YangMillsGaussianWardTwoDerivativeMaxwellClassificationExact as Ward
import DASHI.Physics.YangMills.YangMillsGaussianWardGapNontrivialityExact as Nontrivial

record MinimalSameFamilyGaussianWardKernel
    {Observable Point Scalar : Set}
    (system : OS.ContinuumSchwingerSystem Observable Point Scalar)
    : Set₁ where
  field
    Gaussian : OS.ContinuumSchwingerSystem Observable Point Scalar → Set

    coefficientAlgebra : Ward.WardCoefficientAdditiveGroup

    localWardKernelUnderGaussian :
      Gaussian system →
      Ward.GenericLocalTwoDerivativeWardKernel coefficientAlgebra

open MinimalSameFamilyGaussianWardKernel public

record MinimalSameHGapBridge
    {Observable Point Scalar : Set}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (local :
      MinimalSameFamilyGaussianWardKernel system)
    : Set₂ where
  field
    reconstruction :
      OS.OSReconstructionAuthority Observable Point Scalar system

    gapOrder : Free.GapOrder

    gaussianMaxwellPhysicalSector :
      (gaussian : Gaussian local system) →
      Ward.GenericMaxwellQuadraticKernelClassification
        (coefficientAlgebra local)
        (localWardKernelUnderGaussian local gaussian) →
      Disp.GaplessGaugeInvariantPhysicalSector gapOrder

    PhysicalPositiveGap : OS.Hamiltonian reconstruction → Set

    physicalPositiveGap :
      PhysicalPositiveGap (OS.hamiltonian reconstruction)

    gapRestrictsToSamePhysicalSector :
      (gaussian : Gaussian local system) →
      (classification :
        Ward.GenericMaxwellQuadraticKernelClassification
          (coefficientAlgebra local)
          (localWardKernelUnderGaussian local gaussian)) →
      PhysicalPositiveGap (OS.hamiltonian reconstruction) →
      Free.PositiveSpectralGap
        (Disp.gaugeInvariantPhysicalSectorGivesGaplessApproximation
          (gaussianMaxwellPhysicalSector gaussian classification))

    spectralGapContradictionIsAbsurd :
      (gaussian : Gaussian local system) →
      (classification :
        Ward.GenericMaxwellQuadraticKernelClassification
          (coefficientAlgebra local)
          (localWardKernelUnderGaussian local gaussian)) →
      let sector = gaussianMaxwellPhysicalSector gaussian classification
          gapData =
            gapRestrictsToSamePhysicalSector
              gaussian classification physicalPositiveGap
      in
      Free.SpectralContradiction gapData → ⊥

open MinimalSameHGapBridge public

asSameSystemGaussianWardGapData :
  ∀ {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (local : MinimalSameFamilyGaussianWardKernel system) →
  MinimalSameHGapBridge local →
  Nontrivial.SameSystemGaussianWardGapData system
asSameSystemGaussianWardGapData local bridge = record
  { Nontrivial.SameSystemGaussianWardGapData.reconstruction =
      reconstruction bridge
  ; Nontrivial.SameSystemGaussianWardGapData.Gaussian =
      Gaussian local
  ; Nontrivial.SameSystemGaussianWardGapData.coefficientAlgebra =
      coefficientAlgebra local
  ; Nontrivial.SameSystemGaussianWardGapData.localWardKernelUnderGaussian =
      localWardKernelUnderGaussian local
  ; Nontrivial.SameSystemGaussianWardGapData.gapOrder =
      gapOrder bridge
  ; Nontrivial.SameSystemGaussianWardGapData.gaussianMaxwellPhysicalSector =
      gaussianMaxwellPhysicalSector bridge
  ; Nontrivial.SameSystemGaussianWardGapData.PhysicalPositiveGap =
      PhysicalPositiveGap bridge
  ; Nontrivial.SameSystemGaussianWardGapData.physicalPositiveGap =
      physicalPositiveGap bridge
  ; Nontrivial.SameSystemGaussianWardGapData.gapRestrictsToSamePhysicalSector =
      gapRestrictsToSamePhysicalSector bridge
  ; Nontrivial.SameSystemGaussianWardGapData.spectralGapContradictionIsAbsurd =
      spectralGapContradictionIsAbsurd bridge
  }

minimalInteractingWitness :
  ∀ {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (local : MinimalSameFamilyGaussianWardKernel system) →
  MinimalSameHGapBridge local →
  OS.InteractingContinuumWitness Observable Point Scalar system
minimalInteractingWitness local bridge =
  Nontrivial.nonGaussianityGivesInteractingContinuumWitness
    (asSameSystemGaussianWardGapData local bridge)

round549MinimalNontrivialityCompilerLevel : ProofLevel
round549MinimalNontrivialityCompilerLevel =
  Nontrivial.gaussianGapNontrivialityCompilerLevel

round549WardMaxwellClassificationCompilerLevel : ProofLevel
round549WardMaxwellClassificationCompilerLevel =
  Nontrivial.wardMaxwellCoefficientCompilerLevel

round549GaussianMaxwellSameHSpectralAuthorityLevel : ProofLevel
round549GaussianMaxwellSameHSpectralAuthorityLevel =
  Nontrivial.gaussianOSMaxwellGaugeInvariantCompositeReconstructionLevel

-- Genuine local source content on the shortest H6 route.
literalRound549MinimalSameFamilyWardKernelLevel : ProofLevel
literalRound549MinimalSameFamilyWardKernelLevel = conditional

-- Full OPE/stress closure is not consumed by this reductio compiler.
fullOPEStressPackageRequiredForH6Contradiction : Agda.Builtin.Bool.Bool
fullOPEStressPackageRequiredForH6Contradiction = Agda.Builtin.Bool.false
