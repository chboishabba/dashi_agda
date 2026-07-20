module DASHI.Physics.YangMills.BalabanMassGapSurvival where

------------------------------------------------------------------------
-- Survival of a positive cutoff gap in the continuum limit.
--
-- The finite-cutoff spectral statements, one common positive lower bound, and
-- the spectral-convergence theorem are separate inputs.  The final physical
-- mass-gap certificate is assembled only after all three are present.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap

record UniformCutoffGapData
    (Cutoff Hamiltonian Bound : Set) : Set₁ where
  field
    cutoffHamiltonian : Cutoff → Hamiltonian
    cutoffGap : Cutoff → Bound
    lowerGap : Bound

    Positive : Bound → Set
    LessEqual : Bound → Bound → Set
    positiveLowerGap : Positive lowerGap
    lowerBoundUniform : ∀ cutoff → LessEqual lowerGap (cutoffGap cutoff)

    SpectrumSeparatedBy : Hamiltonian → Bound → Set
    cutoffSpectrumSeparated : ∀ cutoff →
      SpectrumSeparatedBy (cutoffHamiltonian cutoff) (cutoffGap cutoff)

open UniformCutoffGapData public

record GapSurvivesContinuumAuthority
    {Cutoff Hamiltonian Bound : Set}
    (dataSet : UniformCutoffGapData Cutoff Hamiltonian Bound) : Set₁ where
  field
    continuumHamiltonian : Hamiltonian
    uniformGapTransfer :
      (∀ cutoff → LessEqual dataSet (lowerGap dataSet) (cutoffGap dataSet cutoff)) →
      (∀ cutoff →
        SpectrumSeparatedBy dataSet
          (cutoffHamiltonian dataSet cutoff)
          (cutoffGap dataSet cutoff)) →
      SpectrumSeparatedBy dataSet continuumHamiltonian (lowerGap dataSet)

open GapSurvivesContinuumAuthority public

survivingPhysicalMassGap :
  ∀ {Cutoff Hamiltonian Bound : Set} →
  (dataSet : UniformCutoffGapData Cutoff Hamiltonian Bound) →
  GapSurvivesContinuumAuthority dataSet →
  OSGap.PhysicalMassGapCertificate Hamiltonian Bound
survivingPhysicalMassGap dataSet authority = record
  { hamiltonian = continuumHamiltonian authority
  ; gap = lowerGap dataSet
  ; Positive = Positive dataSet
  ; gapPositive = positiveLowerGap dataSet
  ; SpectrumAboveVacuumGap =
      SpectrumSeparatedBy dataSet
        (continuumHamiltonian authority) (lowerGap dataSet)
  ; spectrumAboveVacuumGap =
      uniformGapTransfer authority
        (lowerBoundUniform dataSet)
        (cutoffSpectrumSeparated dataSet)
  }

massGapSurvivalAssemblyLevel : ProofLevel
massGapSurvivalAssemblyLevel = machineChecked

spectralGapTransferAuthorityLevel : ProofLevel
spectralGapTransferAuthorityLevel = standardImported

uniformPositiveCutoffGapInputsLevel : ProofLevel
uniformPositiveCutoffGapInputsLevel = conjectural
