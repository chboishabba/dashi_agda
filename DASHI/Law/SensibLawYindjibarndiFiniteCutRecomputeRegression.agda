module DASHI.Law.SensibLawYindjibarndiFiniteCutRecomputeRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawYindjibarndiFiniteCutRecomputeExact as Y

supportCutRemainsComputed :
  Y.supportSnapshotHasMeaningfulCut
    Y.canonicalYindjibarndiFiniteCutRecomputeBoundary
  ≡ true
supportCutRemainsComputed = refl

defeatedSnapshotStillRoutesToRepair :
  Y.defeatedSnapshotRoutesToRepair
    Y.canonicalYindjibarndiFiniteCutRecomputeBoundary
  ≡ true
defeatedSnapshotStillRoutesToRepair = refl

maboOnlyRepairStillDoesNotReopen :
  Y.maboOnlyRepairStillRoutesToRepair
    Y.canonicalYindjibarndiFiniteCutRecomputeBoundary
  ≡ true
maboOnlyRepairStillDoesNotReopen = refl

fullCandidateRepairStillRecomputesCut :
  Y.fullyRepairedCandidateRecomputesCut
    Y.canonicalYindjibarndiFiniteCutRecomputeBoundary
  ≡ true
fullCandidateRepairStillRecomputesCut = refl

cutIdentityStillChanges :
  Y.recomputedCutIdentityChanges
    Y.canonicalYindjibarndiFiniteCutRecomputeBoundary
  ≡ true
cutIdentityStillChanges = refl

recomputedCutStillDoesNotCreateLaw :
  Y.recomputedCutCreatesCurrentLaw
    Y.canonicalYindjibarndiFiniteCutRecomputeBoundary
  ≡ false
recomputedCutStillDoesNotCreateLaw = refl

oldCutStillCannotBeFrozen :
  Y.OldCutMayBeReusedAfterRefinementWithoutRecompute → ⊥
oldCutStillCannotBeFrozen =
  Y.oldCutCannotBeFrozenAcrossRefinement
