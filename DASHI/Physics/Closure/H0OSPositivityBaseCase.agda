module DASHI.Physics.Closure.H0OSPositivityBaseCase where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.OSPositivityFromRGFixedPoint as OSRG

------------------------------------------------------------------------
-- H0 OS-positivity base-case diagnostic.
--
-- The selected numerical H0 matrix below uses the currently explicit
-- p2/p3/p5 diagonal depth energies and the explicit 1-2 and 2-3 raw
-- couplings.  The missing 1-3 coupling is set to zero only for this selected
-- finite diagnostic:
--
--   [ 6377   866     0 ]
--   [  866  9565  2858 ]  milli-units
--   [    0  2858 15942 ]
--
-- The selected matrix is positive definite by the recorded principal-minor
-- / eigenvalue diagnostic.  This is not yet the full RG-Hamiltonian
-- reflection-positive base case: the actual 1-3 raw coupling and the
-- identification of this PSD matrix with the OS reflection inner-product
-- form are still open.

data H0BaseCaseStatus : Set where
  selectedThreeByThreeMatrixPSDButFullOSBaseStillOpen :
    H0BaseCaseStatus

data H0OSBaseBlocker : Set where
  missingRawP2P5Coupling :
    H0OSBaseBlocker

  missingReflectionInnerProductIdentification :
    H0OSBaseBlocker

  missingAllObservablesPositiveHalfCarrierCheck :
    H0OSBaseBlocker

canonicalH0OSBaseBlockers :
  List H0OSBaseBlocker
canonicalH0OSBaseBlockers =
  missingRawP2P5Coupling
  ∷ missingReflectionInnerProductIdentification
  ∷ missingAllObservablesPositiveHalfCarrierCheck
  ∷ []

data H0OSPromotionFlag : Set where

h0OSPromotionFlagImpossibleHere :
  H0OSPromotionFlag →
  ⊥
h0OSPromotionFlagImpossibleHere ()

h0SelectedMatrixLabel : String
h0SelectedMatrixLabel =
  "[[6377,866,0],[866,9565,2858],[0,2858,15942]] milli-units"

h0SelectedEigenvalueLabel : String
h0SelectedEigenvalueLabel =
  "selected eigenvalues approximately 6093, 8746, 17044 milli-units"

record H0OSPositivityBaseCaseReceipt : Setω where
  field
    osPositivityFromRGReceipt :
      OSRG.OSPositivityFromRGFixedPointReceipt

    status :
      H0BaseCaseStatus

    selectedMatrix :
      String

    selectedMatrixIsCanonical :
      selectedMatrix ≡ h0SelectedMatrixLabel

    diagonalP2Milli :
      Nat

    diagonalP2MilliIs6377 :
      diagonalP2Milli ≡ 6377

    diagonalP3Milli :
      Nat

    diagonalP3MilliIs9565 :
      diagonalP3Milli ≡ 9565

    diagonalP5Milli :
      Nat

    diagonalP5MilliIs15942 :
      diagonalP5Milli ≡ 15942

    offDiagonalP2P3Milli :
      Nat

    offDiagonalP2P3MilliIs866 :
      offDiagonalP2P3Milli ≡ 866

    offDiagonalP3P5Milli :
      Nat

    offDiagonalP3P5MilliIs2858 :
      offDiagonalP3P5Milli ≡ 2858

    selectedOffDiagonalP2P5Milli :
      Nat

    selectedOffDiagonalP2P5MilliIsZero :
      selectedOffDiagonalP2P5Milli ≡ 0

    leadingPrincipalMinor1Positive :
      Bool

    leadingPrincipalMinor1PositiveIsTrue :
      leadingPrincipalMinor1Positive ≡ true

    leadingPrincipalMinor2Positive :
      Bool

    leadingPrincipalMinor2PositiveIsTrue :
      leadingPrincipalMinor2Positive ≡ true

    determinantPositive :
      Bool

    determinantPositiveIsTrue :
      determinantPositive ≡ true

    selectedEigenvalueDiagnostic :
      String

    selectedEigenvalueDiagnosticIsCanonical :
      selectedEigenvalueDiagnostic ≡ h0SelectedEigenvalueLabel

    selectedMatrixPositiveDefinite :
      Bool

    selectedMatrixPositiveDefiniteIsTrue :
      selectedMatrixPositiveDefinite ≡ true

    fullRawHamiltonianMatrixConstructed :
      Bool

    fullRawHamiltonianMatrixConstructedIsFalse :
      fullRawHamiltonianMatrixConstructed ≡ false

    h0OSPositivityBaseCaseInhabited :
      Bool

    h0OSPositivityBaseCaseInhabitedIsFalse :
      h0OSPositivityBaseCaseInhabited ≡ false

    osPositivityInhabitedUnconditionally :
      Bool

    osPositivityInhabitedUnconditionallyIsFalse :
      osPositivityInhabitedUnconditionally ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    blockers :
      List H0OSBaseBlocker

    blockersAreCanonical :
      blockers ≡ canonicalH0OSBaseBlockers

    promotionFlags :
      List H0OSPromotionFlag

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open H0OSPositivityBaseCaseReceipt public

canonicalH0OSPositivityBaseCaseReceipt :
  H0OSPositivityBaseCaseReceipt
canonicalH0OSPositivityBaseCaseReceipt =
  record
    { osPositivityFromRGReceipt =
        OSRG.canonicalOSPositivityFromRGFixedPointReceipt
    ; status =
        selectedThreeByThreeMatrixPSDButFullOSBaseStillOpen
    ; selectedMatrix =
        h0SelectedMatrixLabel
    ; selectedMatrixIsCanonical =
        refl
    ; diagonalP2Milli =
        6377
    ; diagonalP2MilliIs6377 =
        refl
    ; diagonalP3Milli =
        9565
    ; diagonalP3MilliIs9565 =
        refl
    ; diagonalP5Milli =
        15942
    ; diagonalP5MilliIs15942 =
        refl
    ; offDiagonalP2P3Milli =
        866
    ; offDiagonalP2P3MilliIs866 =
        refl
    ; offDiagonalP3P5Milli =
        2858
    ; offDiagonalP3P5MilliIs2858 =
        refl
    ; selectedOffDiagonalP2P5Milli =
        0
    ; selectedOffDiagonalP2P5MilliIsZero =
        refl
    ; leadingPrincipalMinor1Positive =
        true
    ; leadingPrincipalMinor1PositiveIsTrue =
        refl
    ; leadingPrincipalMinor2Positive =
        true
    ; leadingPrincipalMinor2PositiveIsTrue =
        refl
    ; determinantPositive =
        true
    ; determinantPositiveIsTrue =
        refl
    ; selectedEigenvalueDiagnostic =
        h0SelectedEigenvalueLabel
    ; selectedEigenvalueDiagnosticIsCanonical =
        refl
    ; selectedMatrixPositiveDefinite =
        true
    ; selectedMatrixPositiveDefiniteIsTrue =
        refl
    ; fullRawHamiltonianMatrixConstructed =
        false
    ; fullRawHamiltonianMatrixConstructedIsFalse =
        refl
    ; h0OSPositivityBaseCaseInhabited =
        false
    ; h0OSPositivityBaseCaseInhabitedIsFalse =
        refl
    ; osPositivityInhabitedUnconditionally =
        false
    ; osPositivityInhabitedUnconditionallyIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; blockers =
        canonicalH0OSBaseBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The selected 3x3 H0 matrix with p2-p5 coupling set to zero is positive definite"
        ∷ "This proves only a selected finite PSD diagnostic"
        ∷ "The raw p2-p5 coupling and the OS reflection inner-product identification are still missing"
        ∷ "OS positivity, Wightman reconstruction, and Clay Yang-Mills promotion remain false"
        ∷ []
    }

h0SelectedMatrixPositiveDefinite :
  selectedMatrixPositiveDefinite canonicalH0OSPositivityBaseCaseReceipt
  ≡
  true
h0SelectedMatrixPositiveDefinite =
  refl

h0FullOSBaseCaseStillOpen :
  h0OSPositivityBaseCaseInhabited canonicalH0OSPositivityBaseCaseReceipt
  ≡
  false
h0FullOSBaseCaseStillOpen =
  refl

h0OSBaseDoesNotPromoteClay :
  clayYangMillsPromoted canonicalH0OSPositivityBaseCaseReceipt
  ≡
  false
h0OSBaseDoesNotPromoteClay =
  refl
