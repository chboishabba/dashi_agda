module DASHI.Physics.Closure.OSPositivityCorrectObjectReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierVEVReceipt as VEV
import DASHI.Physics.Closure.MassiveSubspaceOSPositivity as Massive
import DASHI.Physics.Closure.OSAxiomsContinuumStatus as OSStatus

data OSPositiveCarrierObject : Set where
  scalarHiggsW4TransferMatrix : OSPositiveCarrierObject
  quarkYukawaMatrixNotHamiltonian : OSPositiveCarrierObject

data OSCorrectObjectBlocker : Set where
  fermionPhysicalMassMatrixStillConditional : OSCorrectObjectBlocker
  continuumReflectionPositivityStillOpen : OSCorrectObjectBlocker
  wightmanReconstructionStillOpen : OSCorrectObjectBlocker

canonicalOSCorrectObjectBlockers :
  List OSCorrectObjectBlocker
canonicalOSCorrectObjectBlockers =
  fermionPhysicalMassMatrixStillConditional
  ∷ continuumReflectionPositivityStillOpen
  ∷ wightmanReconstructionStillOpen
  ∷ []

osCorrectObjectStatement : String
osCorrectObjectStatement =
  "The raw quark Yukawa matrix is not the OS Hamiltonian.  The scalar/Higgs/W4 transfer matrix e^{-a sqrt(p^2+M_H^2)} is the OS-positive object; fermionic OS positivity remains conditional on the physical mass matrix."

record OSPositivityCorrectObjectReceipt : Setω where
  field
    massiveSubspaceReceipt :
      Massive.MassiveSubspaceOSPositivityReceipt

    yukawaNotHamiltonianAlreadyRecorded :
      Massive.yukawaCouplingsNotHamiltonianEntries massiveSubspaceReceipt
      ≡
      true

    carrierVEVReceipt :
      VEV.CarrierVEVReceipt

    physicalMassMatrixStillOpen :
      VEV.physicalMassMatrixFromVEV carrierVEVReceipt ≡ false

    priorOSAxiomStatus :
      OSStatus.OSAxiomsContinuumStatusReceipt

    wightmanStillOpen :
      OSStatus.wightmanReconstructionApplied priorOSAxiomStatus ≡ false

    scalarOSObject :
      OSPositiveCarrierObject

    scalarOSObjectIsCanonical :
      scalarOSObject ≡ scalarHiggsW4TransferMatrix

    quarkMatrixClassification :
      OSPositiveCarrierObject

    quarkMatrixClassificationIsCanonical :
      quarkMatrixClassification ≡ quarkYukawaMatrixNotHamiltonian

    scalarTransferMatrixOSPositive :
      Bool

    scalarTransferMatrixOSPositiveIsTrue :
      scalarTransferMatrixOSPositive ≡ true

    h0QuarkSectorMisidentificationCorrected :
      Bool

    h0QuarkSectorMisidentificationCorrectedIsTrue :
      h0QuarkSectorMisidentificationCorrected ≡ true

    osPositivityForScalarSector :
      Bool

    osPositivityForScalarSectorIsTrue :
      osPositivityForScalarSector ≡ true

    osPositivityForFermionSector :
      Bool

    osPositivityForFermionSectorIsFalse :
      osPositivityForFermionSector ≡ false

    fullOSPositivityInhabited :
      Bool

    fullOSPositivityInhabitedIsFalse :
      fullOSPositivityInhabited ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    blockers :
      List OSCorrectObjectBlocker

    blockersAreCanonical :
      blockers ≡ canonicalOSCorrectObjectBlockers

    statement :
      String

    statementIsCanonical :
      statement ≡ osCorrectObjectStatement

    receiptBoundary :
      List String

open OSPositivityCorrectObjectReceipt public

canonicalOSPositivityCorrectObjectReceipt :
  OSPositivityCorrectObjectReceipt
canonicalOSPositivityCorrectObjectReceipt =
  record
    { massiveSubspaceReceipt =
        Massive.canonicalMassiveSubspaceOSPositivityReceipt
    ; yukawaNotHamiltonianAlreadyRecorded =
        refl
    ; carrierVEVReceipt =
        VEV.canonicalCarrierVEVReceipt
    ; physicalMassMatrixStillOpen =
        refl
    ; priorOSAxiomStatus =
        OSStatus.canonicalOSAxiomsContinuumStatusReceipt
    ; wightmanStillOpen =
        refl
    ; scalarOSObject =
        scalarHiggsW4TransferMatrix
    ; scalarOSObjectIsCanonical =
        refl
    ; quarkMatrixClassification =
        quarkYukawaMatrixNotHamiltonian
    ; quarkMatrixClassificationIsCanonical =
        refl
    ; scalarTransferMatrixOSPositive =
        true
    ; scalarTransferMatrixOSPositiveIsTrue =
        refl
    ; h0QuarkSectorMisidentificationCorrected =
        true
    ; h0QuarkSectorMisidentificationCorrectedIsTrue =
        refl
    ; osPositivityForScalarSector =
        true
    ; osPositivityForScalarSectorIsTrue =
        refl
    ; osPositivityForFermionSector =
        false
    ; osPositivityForFermionSectorIsFalse =
        refl
    ; fullOSPositivityInhabited =
        false
    ; fullOSPositivityInhabitedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; blockers =
        canonicalOSCorrectObjectBlockers
    ; blockersAreCanonical =
        refl
    ; statement =
        osCorrectObjectStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The scalar/W4 transfer matrix is recorded as OS-positive at the finite object level"
        ∷ "The quark Yukawa matrix is explicitly removed as a candidate Hamiltonian matrix"
        ∷ "Fermion-sector OS positivity, continuum reflection positivity, Wightman reconstruction, and Clay promotion remain false"
        ∷ []
    }

scalarOSPositivityRecorded :
  osPositivityForScalarSector canonicalOSPositivityCorrectObjectReceipt ≡ true
scalarOSPositivityRecorded =
  refl
