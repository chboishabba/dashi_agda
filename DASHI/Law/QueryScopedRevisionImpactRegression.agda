module DASHI.Law.QueryScopedRevisionImpactRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.QueryScopedRevisionImpactExact as Impact

boundary : Impact.QueryScopedRevisionImpactBoundary
boundary = Impact.canonicalQueryScopedRevisionImpactBoundary

irrelevantWorldChangePreservesProjection :
  Impact.worldChangeOutsideQuerySliceMayPreserveProjection boundary ≡ true
irrelevantWorldChangePreservesProjection =
  Impact.worldChangeOutsideQuerySliceMayPreserveProjectionIsTrue boundary

irrelevantWorldChangeDoesNotReopen :
  Impact.worldChangeOutsideQuerySliceReopensConsumerResearch boundary ≡ false
irrelevantWorldChangeDoesNotReopen =
  Impact.worldChangeOutsideQuerySliceReopensConsumerResearchIsFalse boundary

relevantWorldChangeMayChangeProjection :
  Impact.worldChangeInsideQuerySliceMayChangeProjection boundary ≡ true
relevantWorldChangeMayChangeProjection =
  Impact.worldChangeInsideQuerySliceMayChangeProjectionIsTrue boundary

relevantWorldChangeMayReopen :
  Impact.worldChangeInsideQuerySliceMayReopenConsumerResearch boundary ≡ true
relevantWorldChangeMayReopen =
  Impact.worldChangeInsideQuerySliceMayReopenConsumerResearchIsTrue boundary

noAuthorityPromotion :
  Impact.queryScopedImpactCreatesSemanticAuthority boundary ≡ false
noAuthorityPromotion =
  Impact.queryScopedImpactCreatesSemanticAuthorityIsFalse boundary

noClaimTruthPromotion :
  Impact.queryScopedImpactCreatesClaimTruth boundary ≡ false
noClaimTruthPromotion =
  Impact.queryScopedImpactCreatesClaimTruthIsFalse boundary
