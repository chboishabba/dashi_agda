module DASHI.Biology.SourceCueTruthNoncollapseRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Biology.SourceCueTruthNoncollapseExact as X

sourceCueEffectRetained :
  X.healthProfessionalCueRaisedPerceivedReliability X.canonicalSourceCueReliabilityReceipt ≡ true
sourceCueEffectRetained = refl

credibilityMediationRetained :
  X.effectLargelyExplainedByPerceivedSourceCredibility X.canonicalSourceCueReliabilityReceipt ≡ true
credibilityMediationRetained = refl

engagementCueNullRetained :
  X.highEngagementRaisedMisleadingPostReliability X.canonicalSourceCueReliabilityReceipt ≡ false
engagementCueNullRetained = refl

claimAccuracyNotChangedBySourceCue :
  X.sourceCueChangesClaimAccuracy X.canonicalSourceCueTruthBoundary ≡ false
claimAccuracyNotChangedBySourceCue = refl

perceivedReliabilityNotTruthAuthority :
  X.perceivedReliabilityCreatesTruthAuthority X.canonicalSourceCueTruthBoundary ≡ false
perceivedReliabilityNotTruthAuthority = refl

sourceCredibilityNotTruth : X.SourceCredibilityDeterminesTruthPermission → ⊥
sourceCredibilityNotTruth = X.sourceCredibilityDoesNotDetermineTruth
