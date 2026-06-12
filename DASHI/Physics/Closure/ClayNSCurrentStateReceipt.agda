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
  candidatePackageExplicitPromotionEvidenceOpen :
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
  "Current Clay NS state: the Leray weak-solution branch and the candidate-complete self-contained A1-A9 package are explicit, the classical theorem intake is explicit, and the remaining issue is exact promotion evidence for the consumed norms/constants package into accepted continuum regularity and Clay closure; all promotion flags remain false."

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
        candidatePackageExplicitPromotionEvidenceOpen
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
        "The Leray weak-solution branch is true and the candidate-complete self-contained A1-A9 package is explicit at receipt scope"
        ∷ "The classical theorem intake is explicit here; the issue is not missing theorem-shape grammar"
        ∷ "Finite-depth regularity rungs and consumed norms/constants are recorded, but exact promotion evidence into accepted continuum regularity is still missing"
        ∷ "Critical Besov/vorticity control, uniform BKM/vorticity control, global smooth regularity, and Clay closure remain fail-closed"
        ∷ []
    }

clayNSCurrentStateKeepsClayFalse :
  clayNavierStokesPromoted canonicalClayNSCurrentStateReceipt ≡ false
clayNSCurrentStateKeepsClayFalse =
  refl
