module Ontology.DNA.SupervoxelChemistryLongWindowLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Sigma using (fst; snd)

import Ontology.DNA.CrossoverAttachmentSurface as CAS
import Ontology.DNA.StreamingEncoderSurface as SES
import Ontology.DNA.SupervoxelAdmissibility as SA
import Ontology.DNA.ChemistryUVConcrete as UVC

------------------------------------------------------------------------
-- Longer-window chemistry-facing supervoxel law surface for the localized
-- DNA-first lane. This remains theorem-thin: it packages exact alignment
-- between 256-window streaming checksums and the paired supervoxel checksum,
-- together with reverse-complement chemistry witnesses already owned by the
-- supervoxel layer.

record SupervoxelChemistryLongWindowLawSurface : Set₁ where
  field
    attachment : CAS.CrossoverAttachmentSurface
    admissibility : SA.SupervoxelAdmissibilitySurface

    leftStreamingThermoCanonical :
      (sv : SA.Supervoxel256) →
      fst
        (SES.StreamingEncoderSurface.checksumSurface
          (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
          (SES.stateOf (SA.Supervoxel256.leftVoxel sv)))
      ≡
      SES.EncoderState.thermoState
        (SES.stateOf (SA.Supervoxel256.leftVoxel sv))

    rightStreamingThermoCanonical :
      (sv : SA.Supervoxel256) →
      fst
        (SES.StreamingEncoderSurface.checksumSurface
          (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
          (SES.stateOf (SA.Supervoxel256.rightVoxel sv)))
      ≡
      SES.EncoderState.thermoState
        (SES.stateOf (SA.Supervoxel256.rightVoxel sv))

    leftStreamingHamiltonianCanonical :
      (sv : SA.Supervoxel256) →
      snd
        (SES.StreamingEncoderSurface.checksumSurface
          (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
          (SES.stateOf (SA.Supervoxel256.leftVoxel sv)))
      ≡
      SA.SupervoxelChecksum.leftHamiltonian (SA.supervoxelChecksum sv)

    rightStreamingHamiltonianCanonical :
      (sv : SA.Supervoxel256) →
      snd
        (SES.StreamingEncoderSurface.checksumSurface
          (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
          (SES.stateOf (SA.Supervoxel256.rightVoxel sv)))
      ≡
      SA.SupervoxelChecksum.rightHamiltonian (SA.supervoxelChecksum sv)

    supervoxelChecksumConvolutionCanonical :
      (sv : SA.Supervoxel256) →
      SA.SupervoxelAdmissibilitySurface.checksum admissibility sv
      ≡
      SA.superChecksum
        (snd
          (SES.StreamingEncoderSurface.checksumSurface
            (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
            (SES.stateOf (SA.Supervoxel256.leftVoxel sv))))
        (snd
          (SES.StreamingEncoderSurface.checksumSurface
            (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
            (SES.stateOf (SA.Supervoxel256.rightVoxel sv))))
        (UVC.uvKernelConcrete (SA.Supervoxel256.leftVoxel sv)
          + UVC.uvKernelConcrete (SA.Supervoxel256.rightVoxel sv))

    swapRCLeftStreamingHamiltonianCanonical :
      (sv : SA.Supervoxel256) →
      SA.SupervoxelChecksum.leftHamiltonian
        (SA.supervoxelChecksum (SA.swapRC sv))
      ≡
      snd
        (SES.StreamingEncoderSurface.checksumSurface
          (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
          (SES.stateOf
            (SA.reverseComplement256 (SA.Supervoxel256.rightVoxel sv))))

    swapRCRightStreamingHamiltonianCanonical :
      (sv : SA.Supervoxel256) →
      SA.SupervoxelChecksum.rightHamiltonian
        (SA.supervoxelChecksum (SA.swapRC sv))
      ≡
      snd
        (SES.StreamingEncoderSurface.checksumSurface
          (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
          (SES.stateOf
            (SA.reverseComplement256 (SA.Supervoxel256.leftVoxel sv))))

    swapRCUVRiskCanonical :
      (sv : SA.Supervoxel256) →
      SA.SupervoxelChecksum.uvRisk (SA.supervoxelChecksum (SA.swapRC sv))
      ≡
      UVC.uvKernelConcrete (SA.reverseComplement256 (SA.Supervoxel256.rightVoxel sv))
        + UVC.uvKernelConcrete (SA.reverseComplement256 (SA.Supervoxel256.leftVoxel sv))

leftStreamingThermoCanonicalWitness :
  (sv : SA.Supervoxel256) →
  fst
    (SES.StreamingEncoderSurface.checksumSurface
      (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
      (SES.stateOf (SA.Supervoxel256.leftVoxel sv)))
  ≡
  SES.EncoderState.thermoState
    (SES.stateOf (SA.Supervoxel256.leftVoxel sv))
leftStreamingThermoCanonicalWitness sv = refl

rightStreamingThermoCanonicalWitness :
  (sv : SA.Supervoxel256) →
  fst
    (SES.StreamingEncoderSurface.checksumSurface
      (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
      (SES.stateOf (SA.Supervoxel256.rightVoxel sv)))
  ≡
  SES.EncoderState.thermoState
    (SES.stateOf (SA.Supervoxel256.rightVoxel sv))
rightStreamingThermoCanonicalWitness sv = refl

leftStreamingHamiltonianCanonicalWitness :
  (sv : SA.Supervoxel256) →
  snd
    (SES.StreamingEncoderSurface.checksumSurface
      (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
      (SES.stateOf (SA.Supervoxel256.leftVoxel sv)))
  ≡
  SA.SupervoxelChecksum.leftHamiltonian (SA.supervoxelChecksum sv)
leftStreamingHamiltonianCanonicalWitness sv = refl

rightStreamingHamiltonianCanonicalWitness :
  (sv : SA.Supervoxel256) →
  snd
    (SES.StreamingEncoderSurface.checksumSurface
      (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
      (SES.stateOf (SA.Supervoxel256.rightVoxel sv)))
  ≡
  SA.SupervoxelChecksum.rightHamiltonian (SA.supervoxelChecksum sv)
rightStreamingHamiltonianCanonicalWitness sv = refl

supervoxelChecksumConvolutionCanonicalWitness :
  (sv : SA.Supervoxel256) →
  SA.SupervoxelAdmissibilitySurface.checksum
    SA.supervoxelAdmissibilitySurface
    sv
  ≡
  SA.superChecksum
    (snd
      (SES.StreamingEncoderSurface.checksumSurface
        (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
        (SES.stateOf (SA.Supervoxel256.leftVoxel sv))))
    (snd
      (SES.StreamingEncoderSurface.checksumSurface
        (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
        (SES.stateOf (SA.Supervoxel256.rightVoxel sv))))
    (UVC.uvKernelConcrete (SA.Supervoxel256.leftVoxel sv)
      + UVC.uvKernelConcrete (SA.Supervoxel256.rightVoxel sv))
supervoxelChecksumConvolutionCanonicalWitness sv = refl

swapRCLeftStreamingHamiltonianCanonicalWitness :
  (sv : SA.Supervoxel256) →
  SA.SupervoxelChecksum.leftHamiltonian
    (SA.supervoxelChecksum (SA.swapRC sv))
  ≡
  snd
    (SES.StreamingEncoderSurface.checksumSurface
      (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
      (SES.stateOf
        (SA.reverseComplement256 (SA.Supervoxel256.rightVoxel sv))))
swapRCLeftStreamingHamiltonianCanonicalWitness sv =
  SA.swapRC-leftHamiltonianWitness sv

swapRCRightStreamingHamiltonianCanonicalWitness :
  (sv : SA.Supervoxel256) →
  SA.SupervoxelChecksum.rightHamiltonian
    (SA.supervoxelChecksum (SA.swapRC sv))
  ≡
  snd
    (SES.StreamingEncoderSurface.checksumSurface
      (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
      (SES.stateOf
        (SA.reverseComplement256 (SA.Supervoxel256.leftVoxel sv))))
swapRCRightStreamingHamiltonianCanonicalWitness sv =
  SA.swapRC-rightHamiltonianWitness sv

swapRCUVRiskCanonicalWitness :
  (sv : SA.Supervoxel256) →
  SA.SupervoxelChecksum.uvRisk (SA.supervoxelChecksum (SA.swapRC sv))
  ≡
  UVC.uvKernelConcrete (SA.reverseComplement256 (SA.Supervoxel256.rightVoxel sv))
    + UVC.uvKernelConcrete (SA.reverseComplement256 (SA.Supervoxel256.leftVoxel sv))
swapRCUVRiskCanonicalWitness sv = SA.swapRC-uvRiskWitness sv

supervoxelChemistryLongWindowLawSurface :
  SupervoxelChemistryLongWindowLawSurface
supervoxelChemistryLongWindowLawSurface = record
  { attachment = CAS.crossoverAttachmentSurface
  ; admissibility = SA.supervoxelAdmissibilitySurface
  ; leftStreamingThermoCanonical = leftStreamingThermoCanonicalWitness
  ; rightStreamingThermoCanonical = rightStreamingThermoCanonicalWitness
  ; leftStreamingHamiltonianCanonical = leftStreamingHamiltonianCanonicalWitness
  ; rightStreamingHamiltonianCanonical = rightStreamingHamiltonianCanonicalWitness
  ; supervoxelChecksumConvolutionCanonical =
      supervoxelChecksumConvolutionCanonicalWitness
  ; swapRCLeftStreamingHamiltonianCanonical =
      swapRCLeftStreamingHamiltonianCanonicalWitness
  ; swapRCRightStreamingHamiltonianCanonical =
      swapRCRightStreamingHamiltonianCanonicalWitness
  ; swapRCUVRiskCanonical = swapRCUVRiskCanonicalWitness
  }
