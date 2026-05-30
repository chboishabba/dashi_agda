module DASHI.Physics.Closure.ClayNSCurrentStateReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayMillenniumClosureTargetReceipt as Clay
import DASHI.Physics.Closure.NSRegularityGapReceipt as Gap
import DASHI.Physics.Closure.NSRegularityRoadmapFilledReceipt as Roadmap
import DASHI.Physics.Closure.NSWeakSolutionSummaryReceipt as WeakSummary

data ClayNSCurrentStateStatus : Set where
  weakSolutionBranchTrueRegularityAndClayOpen :
    ClayNSCurrentStateStatus

data ClayNSCurrentStateEntry : Set where
  lerayWeakSolutionBranchTrue :
    ClayNSCurrentStateEntry
  finiteDepthRegularityRungsRecordedEntry :
    ClayNSCurrentStateEntry
  uniformBKMVorticityControlFalse :
    ClayNSCurrentStateEntry
  globalSmoothRegularityFalse :
    ClayNSCurrentStateEntry
  clayNavierStokesFalse :
    ClayNSCurrentStateEntry

canonicalClayNSCurrentStateEntries :
  List ClayNSCurrentStateEntry
canonicalClayNSCurrentStateEntries =
  lerayWeakSolutionBranchTrue
  ∷ finiteDepthRegularityRungsRecordedEntry
  ∷ uniformBKMVorticityControlFalse
  ∷ globalSmoothRegularityFalse
  ∷ clayNavierStokesFalse
  ∷ []

clayNSCurrentStateStatement : String
clayNSCurrentStateStatement =
  "Current Clay NS state: Leray weak-solution branch is true; global smooth regularity, uniform BKM/vorticity control, and Clay closure remain false/open."

record ClayNSCurrentStateReceipt : Setω where
  field
    status :
      ClayNSCurrentStateStatus

    weakSummaryReceipt :
      WeakSummary.NSWeakSolutionSummaryReceipt

    weakSummaryLerayTrue :
      WeakSummary.lerayWeakSolutionBranchAvailable
        weakSummaryReceipt
      ≡
      true

    weakSummaryClayFalse :
      WeakSummary.clayNavierStokesPromoted weakSummaryReceipt ≡ false

    regularityGapReceipt :
      Gap.NSRegularityGapReceipt

    regularityGapFiniteRungsTrue :
      Gap.finiteDepthRegularityRungsRecorded
        regularityGapReceipt
      ≡
      true

    regularityGapSmoothFalse :
      Gap.globalSmoothRegularityProved regularityGapReceipt ≡ false

    roadmapReceipt :
      Roadmap.NSRegularityRoadmapFilledReceipt

    roadmapFilledTrue :
      Roadmap.roadmapFilled roadmapReceipt ≡ true

    roadmapClayFalse :
      Roadmap.clayNavierStokesPromoted roadmapReceipt ≡ false

    clayTargetReceipt :
      Clay.ClayMillenniumClosureTargetReceipt

    clayTargetNSClosedFalse :
      Clay.clayNavierStokesClosed clayTargetReceipt ≡ false

    currentEntries :
      List ClayNSCurrentStateEntry

    currentEntriesAreCanonical :
      currentEntries ≡ canonicalClayNSCurrentStateEntries

    lerayWeakSolutionBranchAvailable :
      Bool

    lerayWeakSolutionBranchAvailableIsTrue :
      lerayWeakSolutionBranchAvailable ≡ true

    finiteDepthRegularityRungsRecorded :
      Bool

    finiteDepthRegularityRungsRecordedIsTrue :
      finiteDepthRegularityRungsRecorded ≡ true

    criticalBesovNextTargetRecorded :
      Bool

    criticalBesovNextTargetRecordedIsTrue :
      criticalBesovNextTargetRecorded ≡ true

    uniformBKMVorticityControlClosed :
      Bool

    uniformBKMVorticityControlClosedIsFalse :
      uniformBKMVorticityControlClosed ≡ false

    globalSmoothRegularityProved :
      Bool

    globalSmoothRegularityProvedIsFalse :
      globalSmoothRegularityProved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ clayNSCurrentStateStatement

    receiptBoundary :
      List String

open ClayNSCurrentStateReceipt public

canonicalClayNSCurrentStateReceipt :
  ClayNSCurrentStateReceipt
canonicalClayNSCurrentStateReceipt =
  record
    { status =
        weakSolutionBranchTrueRegularityAndClayOpen
    ; weakSummaryReceipt =
        WeakSummary.canonicalNSWeakSolutionSummaryReceipt
    ; weakSummaryLerayTrue =
        refl
    ; weakSummaryClayFalse =
        refl
    ; regularityGapReceipt =
        Gap.canonicalNSRegularityGapReceipt
    ; regularityGapFiniteRungsTrue =
        refl
    ; regularityGapSmoothFalse =
        refl
    ; roadmapReceipt =
        Roadmap.canonicalNSRegularityRoadmapFilledReceipt
    ; roadmapFilledTrue =
        refl
    ; roadmapClayFalse =
        refl
    ; clayTargetReceipt =
        Clay.canonicalClayMillenniumClosureTargetReceipt
    ; clayTargetNSClosedFalse =
        refl
    ; currentEntries =
        canonicalClayNSCurrentStateEntries
    ; currentEntriesAreCanonical =
        refl
    ; lerayWeakSolutionBranchAvailable =
        true
    ; lerayWeakSolutionBranchAvailableIsTrue =
        refl
    ; finiteDepthRegularityRungsRecorded =
        true
    ; finiteDepthRegularityRungsRecordedIsTrue =
        refl
    ; criticalBesovNextTargetRecorded =
        true
    ; criticalBesovNextTargetRecordedIsTrue =
        refl
    ; uniformBKMVorticityControlClosed =
        false
    ; uniformBKMVorticityControlClosedIsFalse =
        refl
    ; globalSmoothRegularityProved =
        false
    ; globalSmoothRegularityProvedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        clayNSCurrentStateStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The Leray weak-solution branch is the sole true Clay-NS-adjacent mathematical branch here"
        ∷ "Critical Besov/vorticity control is recorded as the next target, not as a closed theorem"
        ∷ "Finite-depth regularity rungs are recorded but do not imply a continuum regularity theorem"
        ∷ "Uniform BKM/vorticity control, global smooth regularity, and Clay closure remain false"
        ∷ []
    }

clayNSCurrentStateKeepsClayFalse :
  clayNavierStokesPromoted canonicalClayNSCurrentStateReceipt ≡ false
clayNSCurrentStateKeepsClayFalse =
  refl
