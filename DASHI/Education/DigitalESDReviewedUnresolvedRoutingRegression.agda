module DASHI.Education.DigitalESDReviewedUnresolvedRoutingRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDReviewedUnresolvedRoutingExact as Routing

reviewedUnresolvedCannotBecomeInclude :
  Routing.ReviewedUnresolvedCreatesInclusion → ⊥
reviewedUnresolvedCannotBecomeInclude =
  Routing.reviewedUnresolvedDoesNotCreateInclusion

reviewedUnresolvedCannotBecomeExclude :
  Routing.ReviewedUnresolvedCreatesExclusion → ⊥
reviewedUnresolvedCannotBecomeExclude =
  Routing.reviewedUnresolvedDoesNotCreateExclusion

resolutionFullTextCannotCreateAuditAdmission :
  Routing.ScreeningResolutionFullTextCreatesSourceAuditAdmission → ⊥
resolutionFullTextCannotCreateAuditAdmission =
  Routing.screeningResolutionFullTextDoesNotCreateSourceAuditAdmission

reviewedUnresolvedDoesNotReturnToSameQueue :
  Routing.ReviewedUnresolvedMayReturnToTitleAbstractQueue → ⊥
reviewedUnresolvedDoesNotReturnToSameQueue =
  Routing.reviewedUnresolvedDoesNotReturnToTitleAbstractQueue
