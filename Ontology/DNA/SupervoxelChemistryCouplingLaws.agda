module Ontology.DNA.SupervoxelChemistryCouplingLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Sigma using (snd)
open import Relation.Binary.PropositionalEquality using (cong₂)

import Ontology.DNA.SupervoxelChemistryLongWindowLaws as LW
import Ontology.DNA.SupervoxelAdmissibility as SA
import Ontology.DNA.StreamingEncoderSurface as SES
import Ontology.DNA.ChemistrySheetHamiltonian as CSH
import Ontology.DNA.CrossoverAttachmentSurface as CAS

------------------------------------------------------------------------
-- Chemistry-facing coupling surface above the longer-window supervoxel
-- package. This remains theorem-thin: it sharpens the current lane from
-- checksum/reverse-complement witnesses to coupled Hamiltonian and sheet
-- cross-band alignment on the current localized carrier.

record SupervoxelChemistryCouplingLawSurface : Set₁ where
  field
    longWindow : LW.SupervoxelChemistryLongWindowLawSurface

    leftStreamingHamiltonianOwnerCanonical :
      (sv : SA.Supervoxel256) →
      snd
        (SES.StreamingEncoderSurface.checksumSurface
          (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
          (SES.stateOf (SA.Supervoxel256.leftVoxel sv)))
      ≡
      CSH.chemistryHamiltonianOf (SA.Supervoxel256.leftVoxel sv)

    rightStreamingHamiltonianOwnerCanonical :
      (sv : SA.Supervoxel256) →
      snd
        (SES.StreamingEncoderSurface.checksumSurface
          (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
          (SES.stateOf (SA.Supervoxel256.rightVoxel sv)))
      ≡
      CSH.chemistryHamiltonianOf (SA.Supervoxel256.rightVoxel sv)

    leftCrossBandWindowCanonical :
      (sv : SA.Supervoxel256) →
      CSH.crossBandEnergy
        (CSH.sheetCoordinatesOf (SA.Supervoxel256.leftVoxel sv))
      ≡
      CSH.countCrossBandCoupling
        (CSH.SheetCoordinates.uSheet
          (CSH.sheetCoordinatesOf (SA.Supervoxel256.leftVoxel sv)))
        (CSH.SheetCoordinates.vSheet
          (CSH.sheetCoordinatesOf (SA.Supervoxel256.leftVoxel sv)))

    rightCrossBandWindowCanonical :
      (sv : SA.Supervoxel256) →
      CSH.crossBandEnergy
        (CSH.sheetCoordinatesOf (SA.Supervoxel256.rightVoxel sv))
      ≡
      CSH.countCrossBandCoupling
        (CSH.SheetCoordinates.uSheet
          (CSH.sheetCoordinatesOf (SA.Supervoxel256.rightVoxel sv)))
        (CSH.SheetCoordinates.vSheet
          (CSH.sheetCoordinatesOf (SA.Supervoxel256.rightVoxel sv)))

    coupledStreamingHamiltonianCanonical :
      (sv : SA.Supervoxel256) →
      SA.SupervoxelChecksum.leftHamiltonian (SA.supervoxelChecksum sv)
        + SA.SupervoxelChecksum.rightHamiltonian (SA.supervoxelChecksum sv)
      ≡
      snd
        (SES.StreamingEncoderSurface.checksumSurface
          (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
          (SES.stateOf (SA.Supervoxel256.leftVoxel sv)))
        +
      snd
        (SES.StreamingEncoderSurface.checksumSurface
          (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
          (SES.stateOf (SA.Supervoxel256.rightVoxel sv)))

    coupledCrossBandWindowCanonical :
      (sv : SA.Supervoxel256) →
      CSH.crossBandEnergy
        (CSH.sheetCoordinatesOf (SA.Supervoxel256.leftVoxel sv))
        +
      CSH.crossBandEnergy
        (CSH.sheetCoordinatesOf (SA.Supervoxel256.rightVoxel sv))
      ≡
      CSH.countCrossBandCoupling
        (CSH.SheetCoordinates.uSheet
          (CSH.sheetCoordinatesOf (SA.Supervoxel256.leftVoxel sv)))
        (CSH.SheetCoordinates.vSheet
          (CSH.sheetCoordinatesOf (SA.Supervoxel256.leftVoxel sv)))
        +
      CSH.countCrossBandCoupling
        (CSH.SheetCoordinates.uSheet
          (CSH.sheetCoordinatesOf (SA.Supervoxel256.rightVoxel sv)))
        (CSH.SheetCoordinates.vSheet
          (CSH.sheetCoordinatesOf (SA.Supervoxel256.rightVoxel sv)))

    swapRCCoupledStreamingHamiltonianCanonical :
      (sv : SA.Supervoxel256) →
      SA.SupervoxelChecksum.leftHamiltonian
        (SA.supervoxelChecksum (SA.swapRC sv))
        +
      SA.SupervoxelChecksum.rightHamiltonian
        (SA.supervoxelChecksum (SA.swapRC sv))
      ≡
      snd
        (SES.StreamingEncoderSurface.checksumSurface
          (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
          (SES.stateOf
            (SA.reverseComplement256 (SA.Supervoxel256.rightVoxel sv))))
        +
      snd
        (SES.StreamingEncoderSurface.checksumSurface
          (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
          (SES.stateOf
            (SA.reverseComplement256 (SA.Supervoxel256.leftVoxel sv))))

leftStreamingHamiltonianOwnerCanonicalWitness :
  (sv : SA.Supervoxel256) →
  snd
    (SES.StreamingEncoderSurface.checksumSurface
      (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
      (SES.stateOf (SA.Supervoxel256.leftVoxel sv)))
  ≡
  CSH.chemistryHamiltonianOf (SA.Supervoxel256.leftVoxel sv)
leftStreamingHamiltonianOwnerCanonicalWitness sv = refl

rightStreamingHamiltonianOwnerCanonicalWitness :
  (sv : SA.Supervoxel256) →
  snd
    (SES.StreamingEncoderSurface.checksumSurface
      (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
      (SES.stateOf (SA.Supervoxel256.rightVoxel sv)))
  ≡
  CSH.chemistryHamiltonianOf (SA.Supervoxel256.rightVoxel sv)
rightStreamingHamiltonianOwnerCanonicalWitness sv = refl

leftCrossBandWindowCanonicalWitness :
  (sv : SA.Supervoxel256) →
  CSH.crossBandEnergy
    (CSH.sheetCoordinatesOf (SA.Supervoxel256.leftVoxel sv))
  ≡
  CSH.countCrossBandCoupling
    (CSH.SheetCoordinates.uSheet
      (CSH.sheetCoordinatesOf (SA.Supervoxel256.leftVoxel sv)))
    (CSH.SheetCoordinates.vSheet
      (CSH.sheetCoordinatesOf (SA.Supervoxel256.leftVoxel sv)))
leftCrossBandWindowCanonicalWitness sv =
  CSH.crossBandEnergy-sheetCoordinatesOf (SA.Supervoxel256.leftVoxel sv)

rightCrossBandWindowCanonicalWitness :
  (sv : SA.Supervoxel256) →
  CSH.crossBandEnergy
    (CSH.sheetCoordinatesOf (SA.Supervoxel256.rightVoxel sv))
  ≡
  CSH.countCrossBandCoupling
    (CSH.SheetCoordinates.uSheet
      (CSH.sheetCoordinatesOf (SA.Supervoxel256.rightVoxel sv)))
    (CSH.SheetCoordinates.vSheet
      (CSH.sheetCoordinatesOf (SA.Supervoxel256.rightVoxel sv)))
rightCrossBandWindowCanonicalWitness sv =
  CSH.crossBandEnergy-sheetCoordinatesOf (SA.Supervoxel256.rightVoxel sv)

coupledStreamingHamiltonianCanonicalWitness :
  (sv : SA.Supervoxel256) →
  SA.SupervoxelChecksum.leftHamiltonian (SA.supervoxelChecksum sv)
    + SA.SupervoxelChecksum.rightHamiltonian (SA.supervoxelChecksum sv)
  ≡
  snd
    (SES.StreamingEncoderSurface.checksumSurface
      (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
      (SES.stateOf (SA.Supervoxel256.leftVoxel sv)))
    +
  snd
    (SES.StreamingEncoderSurface.checksumSurface
      (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
      (SES.stateOf (SA.Supervoxel256.rightVoxel sv)))
coupledStreamingHamiltonianCanonicalWitness sv = refl

coupledCrossBandWindowCanonicalWitness :
  (sv : SA.Supervoxel256) →
  CSH.crossBandEnergy
    (CSH.sheetCoordinatesOf (SA.Supervoxel256.leftVoxel sv))
    +
  CSH.crossBandEnergy
    (CSH.sheetCoordinatesOf (SA.Supervoxel256.rightVoxel sv))
  ≡
  CSH.countCrossBandCoupling
    (CSH.SheetCoordinates.uSheet
      (CSH.sheetCoordinatesOf (SA.Supervoxel256.leftVoxel sv)))
    (CSH.SheetCoordinates.vSheet
      (CSH.sheetCoordinatesOf (SA.Supervoxel256.leftVoxel sv)))
    +
  CSH.countCrossBandCoupling
    (CSH.SheetCoordinates.uSheet
      (CSH.sheetCoordinatesOf (SA.Supervoxel256.rightVoxel sv)))
    (CSH.SheetCoordinates.vSheet
      (CSH.sheetCoordinatesOf (SA.Supervoxel256.rightVoxel sv)))
coupledCrossBandWindowCanonicalWitness sv =
  cong₂ _+_
    (CSH.crossBandEnergy-sheetCoordinatesOf (SA.Supervoxel256.leftVoxel sv))
    (CSH.crossBandEnergy-sheetCoordinatesOf (SA.Supervoxel256.rightVoxel sv))

swapRCCoupledStreamingHamiltonianCanonicalWitness :
  (sv : SA.Supervoxel256) →
  SA.SupervoxelChecksum.leftHamiltonian
    (SA.supervoxelChecksum (SA.swapRC sv))
    +
  SA.SupervoxelChecksum.rightHamiltonian
    (SA.supervoxelChecksum (SA.swapRC sv))
  ≡
  snd
    (SES.StreamingEncoderSurface.checksumSurface
      (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
      (SES.stateOf
        (SA.reverseComplement256 (SA.Supervoxel256.rightVoxel sv))))
    +
  snd
    (SES.StreamingEncoderSurface.checksumSurface
      (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
      (SES.stateOf
        (SA.reverseComplement256 (SA.Supervoxel256.leftVoxel sv))))
swapRCCoupledStreamingHamiltonianCanonicalWitness sv =
  cong₂ _+_
    (SA.swapRC-leftHamiltonianWitness sv)
    (SA.swapRC-rightHamiltonianWitness sv)

supervoxelChemistryCouplingLawSurface :
  SupervoxelChemistryCouplingLawSurface
supervoxelChemistryCouplingLawSurface = record
  { longWindow = LW.supervoxelChemistryLongWindowLawSurface
  ; leftStreamingHamiltonianOwnerCanonical =
      leftStreamingHamiltonianOwnerCanonicalWitness
  ; rightStreamingHamiltonianOwnerCanonical =
      rightStreamingHamiltonianOwnerCanonicalWitness
  ; leftCrossBandWindowCanonical = leftCrossBandWindowCanonicalWitness
  ; rightCrossBandWindowCanonical = rightCrossBandWindowCanonicalWitness
  ; coupledStreamingHamiltonianCanonical =
      coupledStreamingHamiltonianCanonicalWitness
  ; coupledCrossBandWindowCanonical =
      coupledCrossBandWindowCanonicalWitness
  ; swapRCCoupledStreamingHamiltonianCanonical =
      swapRCCoupledStreamingHamiltonianCanonicalWitness
  }
