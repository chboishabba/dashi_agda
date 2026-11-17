module DASHI.Governance.OccupyOWSManifestRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyOWSManifestExact as Manifest

recordCountPinned : Manifest.recordCount Manifest.canonicalOWSRecords ≡ 45
recordCountPinned = refl

preFreezeInspectedCountPinned : Manifest.recordCount Manifest.preFreezeInspectedRecords ≡ 7
preFreezeInspectedCountPinned = refl

prospectiveHoldoutCountPinned : Manifest.recordCount Manifest.prospectiveHoldoutRecords ≡ 7
prospectiveHoldoutCountPinned = refl

splitManifestHashPinned :
  Manifest.splitManifestSha256
  ≡ "83982d16ef8bce87a3fc7d099203e0ed594e47359b48b9973b7bcb67af0d1bf1"
splitManifestHashPinned = refl

firstProtectedHoldoutPinned : Manifest.OWSRecord
firstProtectedHoldoutPinned = Manifest.record12

lastProtectedHoldoutPinned : Manifest.OWSRecord
lastProtectedHoldoutPinned = Manifest.record42

contentInspectedBeforeFreezeCannotBeHeldOut :
  Manifest.preFreezeInspectedRecordsForcedDevelopment Manifest.canonicalManifestBoundary ≡ true
contentInspectedBeforeFreezeCannotBeHeldOut = refl

headingsMayBeUsedForSplitWithoutOutcomePromotion :
  Manifest.titleDateMetadataTreatedAsOutcome Manifest.canonicalManifestBoundary ≡ false
headingsMayBeUsedForSplitWithoutOutcomePromotion = refl

holdoutContentsRemainUninspectedByManifestConstruction :
  Manifest.holdoutSubstantiveContentsInspectedDuringManifestFreeze Manifest.canonicalManifestBoundary ≡ false
holdoutContentsRemainUninspectedByManifestConstruction = refl
