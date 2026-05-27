module DASHI.Physics.Closure.YukawaFromCarrier where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMCarrierDerived as CKMD
import DASHI.Physics.Closure.CKMExactWitnesses as Exact
import DASHI.Physics.Closure.CKMUnitarityFromCarrier as CKMU
import DASHI.Physics.Closure.HiggsSymmetryBreakingReceipt as Higgs
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.Closure.YukawaDHRIntertwinerCompatibility as YDHR
import DASHI.Physics.YM.FroggattNielsenExpansion as FN

------------------------------------------------------------------------
-- Carrier-derived Yukawa packaging.
--
-- This module does not introduce a new algebraic theory.  It packages the
-- exact 3x3 up/down Yukawa matrices already present in the repository
-- together with the existing FN and Higgs receipts, so downstream Gate 7
-- consumers can read a concrete carrier-side Yukawa surface.

canonicalUpFlavorBasis : List String
canonicalUpFlavorBasis =
  "e_u" ∷ "e_c" ∷ "e_t" ∷ []

canonicalDownFlavorBasis : List String
canonicalDownFlavorBasis =
  "e_d" ∷ "e_s" ∷ "e_b" ∷ []

record CarrierFlavorBasis : Set where
  field
    upBasis :
      List String

    upBasisIsCanonical :
      upBasis ≡ canonicalUpFlavorBasis

    downBasis :
      List String

    downBasisIsCanonical :
      downBasis ≡ canonicalDownFlavorBasis

open CarrierFlavorBasis public

canonicalCarrierFlavorBasis : CarrierFlavorBasis
canonicalCarrierFlavorBasis = record
  { upBasis = canonicalUpFlavorBasis
  ; upBasisIsCanonical = refl
  ; downBasis = canonicalDownFlavorBasis
  ; downBasisIsCanonical = refl
  }

canonicalUpYukawa3x3 : Exact.DiagonalYukawa3x3
canonicalUpYukawa3x3 = Exact.canonicalUpYukawa3x3

canonicalDownYukawa3x3 : Exact.DiagonalYukawa3x3
canonicalDownYukawa3x3 = Exact.canonicalDownYukawa3x3

canonicalUpYukawaMatrix : Matter.MixingMatrix
canonicalUpYukawaMatrix =
  Exact.DiagonalYukawa3x3.matrix canonicalUpYukawa3x3

canonicalDownYukawaMatrix : Matter.MixingMatrix
canonicalDownYukawaMatrix =
  Exact.DiagonalYukawa3x3.matrix canonicalDownYukawa3x3

data YukawaCarrierFailClosedBlocker : Set where
  missingAbsoluteHiggsVEVW4CalibrationForPhysicalYukawa :
    YukawaCarrierFailClosedBlocker

  missingPhysicalFermionMassEigenvalueReceipt :
    YukawaCarrierFailClosedBlocker

  missingSplittingFieldForGenericYukawaEigenvalues :
    YukawaCarrierFailClosedBlocker

  missingEigenbasisTransportForNonDiagonalYukawa :
    YukawaCarrierFailClosedBlocker

  missingPhysicalWeakMassBasisCKMIdentification :
    YukawaCarrierFailClosedBlocker

  missingActualDHRSectorRepresentationsForNonIdentityAction :
    YukawaCarrierFailClosedBlocker

  missingPhysicalYukawaMatricesForDHRPromotion :
    YukawaCarrierFailClosedBlocker

canonicalYukawaCarrierFailClosedBlockers :
  List YukawaCarrierFailClosedBlocker
canonicalYukawaCarrierFailClosedBlockers =
  missingAbsoluteHiggsVEVW4CalibrationForPhysicalYukawa
  ∷ missingPhysicalFermionMassEigenvalueReceipt
  ∷ missingSplittingFieldForGenericYukawaEigenvalues
  ∷ missingEigenbasisTransportForNonDiagonalYukawa
  ∷ missingPhysicalWeakMassBasisCKMIdentification
  ∷ missingActualDHRSectorRepresentationsForNonIdentityAction
  ∷ missingPhysicalYukawaMatricesForDHRPromotion
  ∷ []

record YukawaFromCarrierReceipt : Setω where
  field
    carrierFlavorBasis :
      CarrierFlavorBasis

    fnWitness :
      FN.FroggattNielsenWitness

    higgsReceipt :
      Higgs.HiggsSymmetryBreakingReceipt

    exactWitnessChain :
      Exact.CKMExactWitnessChain

    matterReceipt :
      Matter.MatterRepresentationReceiptSurface

    ckmCarrierDerivedReceipt :
      CKMD.CKMCarrierDerivedReceipt

    ckmUnitaryReceipt :
      CKMU.CKMUnitaryReceipt

    yukawaDHRIntertwinerCompatibilityReceipt :
      YDHR.YukawaDHRIntertwinerCompatibilityReceipt

    carrierDHRYukawaFormulaSurface :
      YDHR.CarrierDHRYukawaFormulaSurface

    carrierDHRYukawaFormulaSurfaceLabel :
      YDHR.formulaLabel carrierDHRYukawaFormulaSurface
      ≡
      "Y_ij = <rho_i, Phi_H * rho_j>"

    ckmCarrierMatrix :
      Matter.MixingMatrix

    ckmCarrierMatrixIsCarrierDerived :
      ckmCarrierMatrix
      ≡
      CKMD.ckmCarrierMatrix ckmCarrierDerivedReceipt

    ckmCarrierMatrixIsUnitaryReceiptMatrix :
      ckmCarrierMatrix
      ≡
      CKMU.carrierCKMMatrix ckmUnitaryReceipt

    ckmCarrierMatrixIsIdentity :
      ckmCarrierMatrix ≡ Matter.identityMixingMatrix

    upYukawa :
      Exact.DiagonalYukawa3x3

    upYukawaIsCanonical :
      upYukawa ≡ canonicalUpYukawa3x3

    downYukawa :
      Exact.DiagonalYukawa3x3

    downYukawaIsCanonical :
      downYukawa ≡ canonicalDownYukawa3x3

    upYukawaMatrix :
      Matter.MixingMatrix

    upYukawaMatrixIsCanonical :
      upYukawaMatrix ≡ canonicalUpYukawaMatrix

    downYukawaMatrix :
      Matter.MixingMatrix

    downYukawaMatrixIsCanonical :
      downYukawaMatrix ≡ canonicalDownYukawaMatrix

    upYukawaMatrixAgreesWithCarrierDerivedCKM :
      upYukawaMatrix
      ≡
      CKMD.yukawaUpMatrix ckmCarrierDerivedReceipt

    downYukawaMatrixAgreesWithCarrierDerivedCKM :
      downYukawaMatrix
      ≡
      CKMD.yukawaDownMatrix ckmCarrierDerivedReceipt

    upYukawaFormulaEntriesAgreeWithMatrix :
      (i j : YDHR.YukawaGenerationIndex) →
      YDHR.upFormulaEntry carrierDHRYukawaFormulaSurface i j
      ≡
      YDHR.matrixEntry upYukawaMatrix i j

    downYukawaFormulaEntriesAgreeWithMatrix :
      (i j : YDHR.YukawaGenerationIndex) →
      YDHR.downFormulaEntry carrierDHRYukawaFormulaSurface i j
      ≡
      YDHR.matrixEntry downYukawaMatrix i j

    carrierDHRYukawaFormulaPhysicalPromotionClosed :
      YDHR.physicalDHRYukawaFormulaPromoted
        carrierDHRYukawaFormulaSurface
      ≡
      false

    yukawaDHRCarrierDerivedReceiptThreaded :
      Bool

    yukawaDHRCarrierDerivedReceiptThreadedIsTrue :
      yukawaDHRCarrierDerivedReceiptThreaded ≡ true

    yukawaDHRIdentitySectorActionExplicit :
      Bool

    yukawaDHRIdentitySectorActionExplicitMatchesReceipt :
      yukawaDHRIdentitySectorActionExplicit
      ≡
      YDHR.identitySectorActionExplicit
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRIdentitySectorActionExplicitIsTrue :
      yukawaDHRIdentitySectorActionExplicit ≡ true

    yukawaDHRNonIdentitySymbolicSectorActionsConstructed :
      Bool

    yukawaDHRNonIdentitySymbolicSectorActionsConstructedMatchesReceipt :
      yukawaDHRNonIdentitySymbolicSectorActionsConstructed
      ≡
      YDHR.nonIdentitySymbolicSectorActionsConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRNonIdentitySymbolicSectorActionsConstructedIsTrue :
      yukawaDHRNonIdentitySymbolicSectorActionsConstructed ≡ true

    yukawaDHRU1PhaseChargeSelectionReceipt :
      YDHR.U1PhaseChargeSelectionSymbolicIntertwinerReceipt

    yukawaDHRU1PhaseChargeSelectionReceiptMatchesDHR :
      yukawaDHRU1PhaseChargeSelectionReceipt
      ≡
      YDHR.u1PhaseChargeSelectionReceipt
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRU1PhaseChargeSelectionConstructed :
      Bool

    yukawaDHRU1PhaseChargeSelectionConstructedMatchesDHR :
      yukawaDHRU1PhaseChargeSelectionConstructed
      ≡
      YDHR.u1PhaseChargeSelectionConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRU1PhaseChargeSelectionConstructedIsTrue :
      yukawaDHRU1PhaseChargeSelectionConstructed ≡ true

    yukawaDHRU1PhysicalSectorRepresentationConstructed :
      Bool

    yukawaDHRU1PhysicalSectorRepresentationConstructedMatchesDHR :
      yukawaDHRU1PhysicalSectorRepresentationConstructed
      ≡
      YDHR.u1PhysicalSectorRepresentationConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRU1PhysicalSectorRepresentationConstructedIsFalse :
      yukawaDHRU1PhysicalSectorRepresentationConstructed ≡ false

    yukawaDHRSU2DoubletShapeReceipt :
      YDHR.SU2DoubletShapeSymbolicIntertwinerReceipt

    yukawaDHRSU2DoubletShapeReceiptMatchesDHR :
      yukawaDHRSU2DoubletShapeReceipt
      ≡
      YDHR.su2DoubletShapeReceipt
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRSU2DoubletShapeCheckConstructed :
      Bool

    yukawaDHRSU2DoubletShapeCheckConstructedMatchesDHR :
      yukawaDHRSU2DoubletShapeCheckConstructed
      ≡
      YDHR.su2DoubletShapeCheckConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRSU2DoubletShapeCheckConstructedIsTrue :
      yukawaDHRSU2DoubletShapeCheckConstructed ≡ true

    yukawaDHRSU2PhysicalMatrixRepresentationConstructed :
      Bool

    yukawaDHRSU2PhysicalMatrixRepresentationConstructedMatchesDHR :
      yukawaDHRSU2PhysicalMatrixRepresentationConstructed
      ≡
      YDHR.su2PhysicalMatrixRepresentationConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRSU2PhysicalMatrixRepresentationConstructedIsFalse :
      yukawaDHRSU2PhysicalMatrixRepresentationConstructed ≡ false

    yukawaDHRPhysicalNonIdentityActionConstructed :
      Bool

    yukawaDHRPhysicalNonIdentityActionConstructedMatchesReceipt :
      yukawaDHRPhysicalNonIdentityActionConstructed
      ≡
      YDHR.physicalNonIdentityDHRActionConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRPhysicalNonIdentityActionConstructedIsFalse :
      yukawaDHRPhysicalNonIdentityActionConstructed ≡ false

    yukawaDHRCarrierCKMMatrixAgrees :
      YDHR.carrierCKMMatrix
        yukawaDHRIntertwinerCompatibilityReceipt
      ≡
      ckmCarrierMatrix

    yukawaDHRUpMatrixAgrees :
      YDHR.upYukawaMatrix
      ≡
      upYukawaMatrix

    yukawaDHRDownMatrixAgrees :
      YDHR.downYukawaMatrix
      ≡
      downYukawaMatrix

    yukawaDHRPhysicalPromotionClosed :
      YDHR.physicalYukawaDHRPromotionConstructed
        yukawaDHRIntertwinerCompatibilityReceipt
      ≡
      false

    yukawaDHRIntertwinerBeyondIdentityClosed :
      YDHR.dhrActionBeyondIdentityConstructed
        yukawaDHRIntertwinerCompatibilityReceipt
      ≡
      false

    yukawaDHRActualSectorRepresentationsConstructed :
      Bool

    yukawaDHRActualSectorRepresentationsConstructedMatchesReceipt :
      yukawaDHRActualSectorRepresentationsConstructed
      ≡
      YDHR.actualDHRSectorRepresentationsConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRActualSectorRepresentationsConstructedIsFalse :
      yukawaDHRActualSectorRepresentationsConstructed ≡ false

    yukawaDHRPhysicalYukawaMatricesSupplied :
      Bool

    yukawaDHRPhysicalYukawaMatricesSuppliedMatchesReceipt :
      yukawaDHRPhysicalYukawaMatricesSupplied
      ≡
      YDHR.physicalYukawaMatricesSupplied
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRPhysicalYukawaMatricesSuppliedIsFalse :
      yukawaDHRPhysicalYukawaMatricesSupplied ≡ false

    failClosedBlockers :
      List YukawaCarrierFailClosedBlocker

    failClosedBlockersAreCanonical :
      failClosedBlockers ≡ canonicalYukawaCarrierFailClosedBlockers

    firstFailClosedBlocker :
      YukawaCarrierFailClosedBlocker

    firstFailClosedBlockerIsAbsoluteHiggsVEVW4 :
      firstFailClosedBlocker
      ≡
      missingAbsoluteHiggsVEVW4CalibrationForPhysicalYukawa

    absoluteHiggsVEVW4CalibrationConstructed :
      Bool

    absoluteHiggsVEVW4CalibrationConstructedIsFalse :
      absoluteHiggsVEVW4CalibrationConstructed ≡ false

    splittingFieldEigenbasisConstructed :
      Bool

    splittingFieldEigenbasisConstructedIsFalse :
      splittingFieldEigenbasisConstructed ≡ false

    physicalYukawaPromotionConstructed :
      Bool

    physicalYukawaPromotionConstructedIsFalse :
      physicalYukawaPromotionConstructed ≡ false

    upSectorLabel :
      String

    upSectorLabelIsCanonical :
      upSectorLabel ≡ "carrier-up-Yukawa"

    downSectorLabel :
      String

    downSectorLabelIsCanonical :
      downSectorLabel ≡ "carrier-down-Yukawa"

    carrierDerivedTargetRecorded :
      Bool

    carrierDerivedTargetRecordedIsTrue :
      carrierDerivedTargetRecorded ≡ true

    boundary :
      List String

open YukawaFromCarrierReceipt public

canonicalYukawaFromCarrier : YukawaFromCarrierReceipt
canonicalYukawaFromCarrier = record
  { carrierFlavorBasis = canonicalCarrierFlavorBasis
  ; fnWitness = FN.canonicalFroggattNielsenWitness
  ; higgsReceipt = Higgs.canonicalHiggsSymmetryBreakingReceipt
  ; exactWitnessChain = Exact.canonicalCKMExactWitnessChain
  ; matterReceipt = Matter.canonicalMatterRepresentationReceiptSurface
  ; ckmCarrierDerivedReceipt = CKMD.canonicalCKMCarrierDerived
  ; ckmUnitaryReceipt = CKMU.canonicalCKMUnitary
  ; yukawaDHRIntertwinerCompatibilityReceipt =
      YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; carrierDHRYukawaFormulaSurface =
      YDHR.carrierDHRYukawaFormulaSurface
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; carrierDHRYukawaFormulaSurfaceLabel =
      refl
  ; ckmCarrierMatrix =
      CKMD.ckmCarrierMatrix CKMD.canonicalCKMCarrierDerived
  ; ckmCarrierMatrixIsCarrierDerived = refl
  ; ckmCarrierMatrixIsUnitaryReceiptMatrix = refl
  ; ckmCarrierMatrixIsIdentity = refl
  ; upYukawa = canonicalUpYukawa3x3
  ; upYukawaIsCanonical = refl
  ; downYukawa = canonicalDownYukawa3x3
  ; downYukawaIsCanonical = refl
  ; upYukawaMatrix = canonicalUpYukawaMatrix
  ; upYukawaMatrixIsCanonical = refl
  ; downYukawaMatrix = canonicalDownYukawaMatrix
  ; downYukawaMatrixIsCanonical = refl
  ; upYukawaMatrixAgreesWithCarrierDerivedCKM = refl
  ; downYukawaMatrixAgreesWithCarrierDerivedCKM = refl
  ; upYukawaFormulaEntriesAgreeWithMatrix =
      λ _ _ → refl
  ; downYukawaFormulaEntriesAgreeWithMatrix =
      λ _ _ → refl
  ; carrierDHRYukawaFormulaPhysicalPromotionClosed =
      refl
  ; yukawaDHRCarrierDerivedReceiptThreaded = true
  ; yukawaDHRCarrierDerivedReceiptThreadedIsTrue = refl
  ; yukawaDHRIdentitySectorActionExplicit =
      YDHR.identitySectorActionExplicit
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRIdentitySectorActionExplicitMatchesReceipt = refl
  ; yukawaDHRIdentitySectorActionExplicitIsTrue = refl
  ; yukawaDHRNonIdentitySymbolicSectorActionsConstructed =
      YDHR.nonIdentitySymbolicSectorActionsConstructed
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRNonIdentitySymbolicSectorActionsConstructedMatchesReceipt =
      refl
  ; yukawaDHRNonIdentitySymbolicSectorActionsConstructedIsTrue =
      refl
  ; yukawaDHRU1PhaseChargeSelectionReceipt =
      YDHR.u1PhaseChargeSelectionReceipt
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRU1PhaseChargeSelectionReceiptMatchesDHR =
      refl
  ; yukawaDHRU1PhaseChargeSelectionConstructed =
      YDHR.u1PhaseChargeSelectionConstructed
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRU1PhaseChargeSelectionConstructedMatchesDHR =
      refl
  ; yukawaDHRU1PhaseChargeSelectionConstructedIsTrue =
      refl
  ; yukawaDHRU1PhysicalSectorRepresentationConstructed =
      YDHR.u1PhysicalSectorRepresentationConstructed
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRU1PhysicalSectorRepresentationConstructedMatchesDHR =
      refl
  ; yukawaDHRU1PhysicalSectorRepresentationConstructedIsFalse =
      refl
  ; yukawaDHRSU2DoubletShapeReceipt =
      YDHR.su2DoubletShapeReceipt
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRSU2DoubletShapeReceiptMatchesDHR =
      refl
  ; yukawaDHRSU2DoubletShapeCheckConstructed =
      YDHR.su2DoubletShapeCheckConstructed
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRSU2DoubletShapeCheckConstructedMatchesDHR =
      refl
  ; yukawaDHRSU2DoubletShapeCheckConstructedIsTrue =
      refl
  ; yukawaDHRSU2PhysicalMatrixRepresentationConstructed =
      YDHR.su2PhysicalMatrixRepresentationConstructed
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRSU2PhysicalMatrixRepresentationConstructedMatchesDHR =
      refl
  ; yukawaDHRSU2PhysicalMatrixRepresentationConstructedIsFalse =
      refl
  ; yukawaDHRPhysicalNonIdentityActionConstructed =
      YDHR.physicalNonIdentityDHRActionConstructed
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRPhysicalNonIdentityActionConstructedMatchesReceipt =
      refl
  ; yukawaDHRPhysicalNonIdentityActionConstructedIsFalse =
      refl
  ; yukawaDHRCarrierCKMMatrixAgrees = refl
  ; yukawaDHRUpMatrixAgrees = refl
  ; yukawaDHRDownMatrixAgrees = refl
  ; yukawaDHRPhysicalPromotionClosed = refl
  ; yukawaDHRIntertwinerBeyondIdentityClosed = refl
  ; yukawaDHRActualSectorRepresentationsConstructed =
      YDHR.actualDHRSectorRepresentationsConstructed
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRActualSectorRepresentationsConstructedMatchesReceipt =
      refl
  ; yukawaDHRActualSectorRepresentationsConstructedIsFalse =
      refl
  ; yukawaDHRPhysicalYukawaMatricesSupplied =
      YDHR.physicalYukawaMatricesSupplied
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRPhysicalYukawaMatricesSuppliedMatchesReceipt =
      refl
  ; yukawaDHRPhysicalYukawaMatricesSuppliedIsFalse =
      refl
  ; failClosedBlockers = canonicalYukawaCarrierFailClosedBlockers
  ; failClosedBlockersAreCanonical = refl
  ; firstFailClosedBlocker =
      missingAbsoluteHiggsVEVW4CalibrationForPhysicalYukawa
  ; firstFailClosedBlockerIsAbsoluteHiggsVEVW4 = refl
  ; absoluteHiggsVEVW4CalibrationConstructed = false
  ; absoluteHiggsVEVW4CalibrationConstructedIsFalse = refl
  ; splittingFieldEigenbasisConstructed = false
  ; splittingFieldEigenbasisConstructedIsFalse = refl
  ; physicalYukawaPromotionConstructed = false
  ; physicalYukawaPromotionConstructedIsFalse = refl
  ; upSectorLabel = "carrier-up-Yukawa"
  ; upSectorLabelIsCanonical = refl
  ; downSectorLabel = "carrier-down-Yukawa"
  ; downSectorLabelIsCanonical = refl
  ; carrierDerivedTargetRecorded = true
  ; carrierDerivedTargetRecordedIsTrue = refl
  ; boundary =
      "The carrier package reuses the exact up/down 3x3 Yukawa matrices already present in CKMExactWitnesses"
      ∷ "FN and Higgs receipts are threaded in as concrete upstream anchors"
      ∷ "The carrier-derived CKM and CKM-unitarity receipts agree on the concrete identity matrix"
      ∷ "MatterRepresentationReceiptSurface is threaded as the matter constructor surface for the quark/Higgs sockets"
      ∷ "The Yukawa/DHR compatibility receipt consumes the same carrier-derived CKM/Yukawa matrices"
      ∷ "The carrier/DHR formula surface exposes Y_ij = <rho_i, Phi_H * rho_j> as concrete up/down matrix-entry access for each generation pair"
      ∷ "The DHR receipt exposes explicit identity-sector coverage plus finite symbolic non-identity sector actions"
      ∷ "The DHR receipt also threads concrete U(1) phase/charge-selection and SU(2) doublet-shape symbolic checks"
      ∷ "Physical fermion masses, absolute Higgs/VEV/W4 calibration, splitting-field/eigenbasis lifts, actual DHR sector representations, and physical Yukawa matrices are explicit fail-closed blockers"
      ∷ "Actual DHR sector representations and physical Yukawa matrices are still absent, so non-identity physical promotion remains false"
      ∷ "Physical non-identity DHR action and physical Yukawa promotion remain fail-closed"
      ∷ "The matrices live in the repo's concrete Matter.MixingMatrix carrier"
      ∷ "No postulate or placeholder field is introduced"
      ∷ []
  }

canonicalYukawaFromCarrierUsesCarrierDerivedCKM :
  ckmCarrierMatrix canonicalYukawaFromCarrier
  ≡
  CKMD.ckmCarrierMatrix
    (ckmCarrierDerivedReceipt canonicalYukawaFromCarrier)
canonicalYukawaFromCarrierUsesCarrierDerivedCKM =
  refl

canonicalYukawaFromCarrierKeepsPhysicalPromotionClosed :
  physicalYukawaPromotionConstructed canonicalYukawaFromCarrier
  ≡
  false
canonicalYukawaFromCarrierKeepsPhysicalPromotionClosed =
  refl

canonicalYukawaFromCarrierThreadsU1PhaseChargeSelection :
  yukawaDHRU1PhaseChargeSelectionConstructed canonicalYukawaFromCarrier
  ≡
  true
canonicalYukawaFromCarrierThreadsU1PhaseChargeSelection =
  refl

canonicalYukawaFromCarrierKeepsU1PhysicalRepresentationClosed :
  yukawaDHRU1PhysicalSectorRepresentationConstructed
    canonicalYukawaFromCarrier
  ≡
  false
canonicalYukawaFromCarrierKeepsU1PhysicalRepresentationClosed =
  refl

canonicalYukawaFromCarrierThreadsSU2DoubletShapeCheck :
  yukawaDHRSU2DoubletShapeCheckConstructed canonicalYukawaFromCarrier
  ≡
  true
canonicalYukawaFromCarrierThreadsSU2DoubletShapeCheck =
  refl

canonicalYukawaFromCarrierKeepsSU2PhysicalRepresentationClosed :
  yukawaDHRSU2PhysicalMatrixRepresentationConstructed
    canonicalYukawaFromCarrier
  ≡
  false
canonicalYukawaFromCarrierKeepsSU2PhysicalRepresentationClosed =
  refl

canonicalYukawaFromCarrierKeepsActualDHRSectorsClosed :
  yukawaDHRActualSectorRepresentationsConstructed
    canonicalYukawaFromCarrier
  ≡
  false
canonicalYukawaFromCarrierKeepsActualDHRSectorsClosed =
  refl

canonicalYukawaFromCarrierKeepsPhysicalMatricesClosed :
  yukawaDHRPhysicalYukawaMatricesSupplied
    canonicalYukawaFromCarrier
  ≡
  false
canonicalYukawaFromCarrierKeepsPhysicalMatricesClosed =
  refl
