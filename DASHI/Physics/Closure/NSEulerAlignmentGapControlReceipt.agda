module DASHI.Physics.Closure.NSEulerAlignmentGapControlReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- NS Euler alignment gap control receipt.
--
-- This module records a conditional route only.  On Omega_K^c in the Euler
-- limit, the eigenvalue-spreading term is tracked as nonpositive and the
-- surviving pressure correction is recorded at the H1^2/delta1 scale.  The
-- strong-gap regime delta1 >> ||u||_H1 is therefore represented as a
-- compressive-alignment route with Pi_c <= 0, but no theorem is discharged,
-- no Clay promotion is claimed, and the explicit blockers remain visible.

data NSEulerAlignmentGapControlStatus : Set where
  conditionalEulerLimitRouteRecorded_noPromotion :
    NSEulerAlignmentGapControlStatus

data NSEulerAlignmentRouteAtom : Set where
  omegaKcRestrictionRecorded :
    NSEulerAlignmentRouteAtom

  eulerLimitRecorded :
    NSEulerAlignmentRouteAtom

  eigenvalueSpreadingTermNonpositive :
    NSEulerAlignmentRouteAtom

  survivingPressureCorrectionAtH1SquaredOverDelta1Scale :
    NSEulerAlignmentRouteAtom

  strongGapDelta1MuchLargerThanUH1Recorded :
    NSEulerAlignmentRouteAtom

  compressiveAlignmentRouteVisible :
    NSEulerAlignmentRouteAtom

  piCNonpositiveConditionalRoute :
    NSEulerAlignmentRouteAtom

canonicalNSEulerAlignmentRouteAtoms :
  List NSEulerAlignmentRouteAtom
canonicalNSEulerAlignmentRouteAtoms =
  omegaKcRestrictionRecorded
  ∷ eulerLimitRecorded
  ∷ eigenvalueSpreadingTermNonpositive
  ∷ survivingPressureCorrectionAtH1SquaredOverDelta1Scale
  ∷ strongGapDelta1MuchLargerThanUH1Recorded
  ∷ compressiveAlignmentRouteVisible
  ∷ piCNonpositiveConditionalRoute
  ∷ []

data NSEulerAlignmentBlocker : Set where
  missingNoncircularDelta1LowerBound :
    NSEulerAlignmentBlocker

  missingUniformH1ToPointwiseGapConversion :
    NSEulerAlignmentBlocker

  missingEulerLimitJustificationForThePressureSign :
    NSEulerAlignmentBlocker

  missingClosedProofOfPiCNonpositive :
    NSEulerAlignmentBlocker

  missingClayAuthority :
    NSEulerAlignmentBlocker

canonicalNSEulerAlignmentBlockers :
  List NSEulerAlignmentBlocker
canonicalNSEulerAlignmentBlockers =
  missingNoncircularDelta1LowerBound
  ∷ missingUniformH1ToPointwiseGapConversion
  ∷ missingEulerLimitJustificationForThePressureSign
  ∷ missingClosedProofOfPiCNonpositive
  ∷ missingClayAuthority
  ∷ []

data NSEulerAlignmentGapControlPromotion : Set where

nseulerAlignmentGapControlPromotionImpossibleHere :
  NSEulerAlignmentGapControlPromotion →
  ⊥
nseulerAlignmentGapControlPromotionImpossibleHere ()

nseulerAlignmentGapControlStatement : String
nseulerAlignmentGapControlStatement =
  "Conditional route only: on Omega_K^c in the Euler limit the eigenvalue-spreading term is recorded as nonpositive, the surviving pressure correction is tracked at H1^2/delta1 scale, and the strong-gap regime delta1 >> ||u||_H1 is the visible compressive-alignment route with Pi_c <= 0; this file does not discharge the needed lower-bound, Euler-reduction, or sign-theorem obligations."

data NSEulerAlignmentRouteBoundary : Set where
  conditionalRouteOnly :
    NSEulerAlignmentRouteBoundary

canonicalNSEulerAlignmentRouteBoundary :
  List NSEulerAlignmentRouteBoundary
canonicalNSEulerAlignmentRouteBoundary =
  conditionalRouteOnly
  ∷ []

record NSEulerAlignmentGapControlReceipt : Setω where
  field
    status :
      NSEulerAlignmentGapControlStatus

    statusIsCanonical :
      status ≡ conditionalEulerLimitRouteRecorded_noPromotion

    routeAtoms :
      List NSEulerAlignmentRouteAtom

    routeAtomsAreCanonical :
      routeAtoms ≡ canonicalNSEulerAlignmentRouteAtoms

    blockers :
      List NSEulerAlignmentBlocker

    blockersAreCanonical :
      blockers ≡ canonicalNSEulerAlignmentBlockers

    omegaKcRestrictionVisible :
      Bool

    omegaKcRestrictionVisibleIsTrue :
      omegaKcRestrictionVisible ≡ true

    eulerLimitVisible :
      Bool

    eulerLimitVisibleIsTrue :
      eulerLimitVisible ≡ true

    eigenvalueSpreadingTermNonpositiveVisible :
      Bool

    eigenvalueSpreadingTermNonpositiveVisibleIsTrue :
      eigenvalueSpreadingTermNonpositiveVisible ≡ true

    survivingPressureCorrectionScaleVisible :
      Bool

    survivingPressureCorrectionScaleVisibleIsTrue :
      survivingPressureCorrectionScaleVisible ≡ true

    strongGapConditionRecorded :
      Bool

    strongGapConditionRecordedIsTrue :
      strongGapConditionRecorded ≡ true

    compressiveAlignmentRouteVisibleFlag :
      Bool

    compressiveAlignmentRouteVisibleFlagIsTrue :
      compressiveAlignmentRouteVisibleFlag ≡ true

    piCNonpositiveConditionalRouteRecorded :
      Bool

    piCNonpositiveConditionalRouteRecordedIsTrue :
      piCNonpositiveConditionalRouteRecorded ≡ true

    piCNonpositiveTheoremProved :
      Bool

    piCNonpositiveTheoremProvedIsFalse :
      piCNonpositiveTheoremProved ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nseulerAlignmentGapControlStatement

    routeBoundary :
      List NSEulerAlignmentRouteBoundary

    routeBoundaryIsCanonical :
      routeBoundary ≡ canonicalNSEulerAlignmentRouteBoundary

    promotions :
      List NSEulerAlignmentGapControlPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSEulerAlignmentGapControlPromotion →
      ⊥

open NSEulerAlignmentGapControlReceipt public

canonicalNSEulerAlignmentGapControlReceipt :
  NSEulerAlignmentGapControlReceipt
canonicalNSEulerAlignmentGapControlReceipt =
  record
    { status =
        conditionalEulerLimitRouteRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; routeAtoms =
        canonicalNSEulerAlignmentRouteAtoms
    ; routeAtomsAreCanonical =
        refl
    ; blockers =
        canonicalNSEulerAlignmentBlockers
    ; blockersAreCanonical =
        refl
    ; omegaKcRestrictionVisible =
        true
    ; omegaKcRestrictionVisibleIsTrue =
        refl
    ; eulerLimitVisible =
        true
    ; eulerLimitVisibleIsTrue =
        refl
    ; eigenvalueSpreadingTermNonpositiveVisible =
        true
    ; eigenvalueSpreadingTermNonpositiveVisibleIsTrue =
        refl
    ; survivingPressureCorrectionScaleVisible =
        true
    ; survivingPressureCorrectionScaleVisibleIsTrue =
        refl
    ; strongGapConditionRecorded =
        true
    ; strongGapConditionRecordedIsTrue =
        refl
    ; compressiveAlignmentRouteVisibleFlag =
        true
    ; compressiveAlignmentRouteVisibleFlagIsTrue =
        refl
    ; piCNonpositiveConditionalRouteRecorded =
        true
    ; piCNonpositiveConditionalRouteRecordedIsTrue =
        refl
    ; piCNonpositiveTheoremProved =
        false
    ; piCNonpositiveTheoremProvedIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; statement =
        nseulerAlignmentGapControlStatement
    ; statementIsCanonical =
        refl
    ; routeBoundary =
        conditionalRouteOnly
        ∷ []
    ; routeBoundaryIsCanonical =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        nseulerAlignmentGapControlPromotionImpossibleHere
    }

