module DASHI.Law.SensibLawOALCLegalFollowAttributionSnowballRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Law.SensibLawOALCLegalFollowAttributionSnowballExact as OALC

oalcBoundaryExists : Set
oalcBoundaryExists = OALC.OalcLegalFollowAttributionBoundary

oalcBoundaryPaid : oalcBoundaryExists
oalcBoundaryPaid = OALC.canonicalOalcLegalFollowAttributionBoundary

partialZeroStillStreams :
  OALC.zeroRowDisposition OALC.partialIndex
    ≡
  OALC.revisionPinnedStreamingRequired
partialZeroStillStreams = OALC.partialZeroRequiresStreaming

citationOnlyCannotRecoverRevision :
  NF.FactorsThrough OALC.citationOnly OALC.exactRevision → ⊥
citationOnlyCannotRecoverRevision =
  OALC.citationOnlyCannotRecoverPinnedRevision

waltonsQidLookupIsOnlyScheduled :
  OALC.qidPriority OALC.apexCourtCase
    ≡
  OALC.qidWorthChecking
waltonsQidLookupIsOnlyScheduled = OALC.waltonsQidPriority
