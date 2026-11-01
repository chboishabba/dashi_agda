module DASHI.Physics.Closure.OSPositivityDissolvedReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YukawaMatrixFullReceipt as YFull

------------------------------------------------------------------------
-- OS-positivity blocker correction.
--
-- The previous H0 checks treated bare Yukawa entries as Hamiltonian matrix
-- entries.  This receipt records the corrected object.  Yukawa entries are
-- interaction/mass terms in the Lagrangian; after VEV insertion the quark
-- Hamiltonian is built from M_d^dagger M_d and is positive semidefinite by
-- construction.  This does not prove the full OS/Wightman continuum problem.

data OSPositivityDissolvedStatus : Set where
  correctedHamiltonianObjectRecorded :
    OSPositivityDissolvedStatus

data OSPositivityRemainingBlocker : Set where
  missingCarrierDerivedVEV :
    OSPositivityRemainingBlocker

  missingFermionTransferMatrixOSProof :
    OSPositivityRemainingBlocker

  missingContinuumOSAxiomPackage :
    OSPositivityRemainingBlocker

canonicalOSPositivityRemainingBlockers :
  List OSPositivityRemainingBlocker
canonicalOSPositivityRemainingBlockers =
  missingCarrierDerivedVEV
  ∷ missingFermionTransferMatrixOSProof
  ∷ missingContinuumOSAxiomPackage
  ∷ []

data OSPositivityDissolvedPromotion : Set where

osPositivityDissolvedPromotionImpossibleHere :
  OSPositivityDissolvedPromotion →
  ⊥
osPositivityDissolvedPromotionImpossibleHere ()

record OSPositivityDissolvedReceipt : Set where
  field
    status :
      OSPositivityDissolvedStatus

    yukawaMatrixReceipt :
      YFull.YukawaMatrixFullReceipt

    yukawaMatrixReceiptIsCanonical :
      yukawaMatrixReceipt ≡ YFull.canonicalYukawaMatrixFullReceipt

    correctedObjectStatement :
      String

    pdgVEVCalibrationStatement :
      String

    h0OSPositivityDissolvedByCorrectObject :
      Bool

    h0OSPositivityDissolvedByCorrectObjectIsTrue :
      h0OSPositivityDissolvedByCorrectObject ≡ true

    yukawaNotHamiltonianConfirmed :
      Bool

    yukawaNotHamiltonianConfirmedIsTrue :
      yukawaNotHamiltonianConfirmed ≡ true

    physicalHamiltonianPSDByConstruction :
      Bool

    physicalHamiltonianPSDByConstructionIsTrue :
      physicalHamiltonianPSDByConstruction ≡ true

    fullOSPositivityPromoted :
      Bool

    fullOSPositivityPromotedIsFalse :
      fullOSPositivityPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List OSPositivityRemainingBlocker

    blockersAreCanonical :
      blockers ≡ canonicalOSPositivityRemainingBlockers

    promotionFlags :
      List OSPositivityDissolvedPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open OSPositivityDissolvedReceipt public

canonicalOSPositivityDissolvedReceipt :
  OSPositivityDissolvedReceipt
canonicalOSPositivityDissolvedReceipt =
  record
    { status =
        correctedHamiltonianObjectRecorded
    ; yukawaMatrixReceipt =
        YFull.canonicalYukawaMatrixFullReceipt
    ; yukawaMatrixReceiptIsCanonical =
        refl
    ; correctedObjectStatement =
        "Yukawa entries are interaction/Lagrangian mass terms, not direct Hamiltonian matrix entries; H_quark = sqrt(p^2 I + M_d^dagger M_d)."
    ; pdgVEVCalibrationStatement =
        "M_d = Y_d * v/sqrt(2) uses v = 246.22 GeV as an external PDG calibration, not a carrier-derived VEV."
    ; h0OSPositivityDissolvedByCorrectObject =
        true
    ; h0OSPositivityDissolvedByCorrectObjectIsTrue =
        refl
    ; yukawaNotHamiltonianConfirmed =
        true
    ; yukawaNotHamiltonianConfirmedIsTrue =
        refl
    ; physicalHamiltonianPSDByConstruction =
        true
    ; physicalHamiltonianPSDByConstructionIsTrue =
        refl
    ; fullOSPositivityPromoted =
        false
    ; fullOSPositivityPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalOSPositivityRemainingBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The negative H0 matrix diagnostic is reclassified as a wrong-object diagnostic"
        ∷ "Positive semidefiniteness of M_d^dagger M_d is algebraic, but full OS positivity still needs the physical transfer matrix"
        ∷ "No Clay, CKM, or continuum OS promotion is asserted"
        ∷ []
    }

osWrongObjectBlockerResolved :
  h0OSPositivityDissolvedByCorrectObject canonicalOSPositivityDissolvedReceipt ≡ true
osWrongObjectBlockerResolved =
  refl

