module DASHI.Law.QueryScopedWorldCoordinateImpactRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.QueryScopedWorldCoordinateImpactExact as Impact

boundary : Impact.QueryScopedWorldCoordinateImpactBoundary
boundary = Impact.canonicalQueryScopedWorldCoordinateImpactBoundary

timeIgnoredWhenUnrequired :
  Impact.unrequiredTimeChangeMayPreserveQueryProjection boundary ≡ true
timeIgnoredWhenUnrequired =
  Impact.unrequiredTimeChangeMayPreserveQueryProjectionIsTrue boundary

timeMattersWhenRequired :
  Impact.requiredTimeChangeMayChangeQueryProjection boundary ≡ true
timeMattersWhenRequired =
  Impact.requiredTimeChangeMayChangeQueryProjectionIsTrue boundary

jurisdictionIgnoredWhenUnrequired :
  Impact.unrequiredJurisdictionChangeMayPreserveQueryProjection boundary ≡ true
jurisdictionIgnoredWhenUnrequired =
  Impact.unrequiredJurisdictionChangeMayPreserveQueryProjectionIsTrue boundary

jurisdictionMattersWhenRequired :
  Impact.requiredJurisdictionChangeMayChangeQueryProjection boundary ≡ true
jurisdictionMattersWhenRequired =
  Impact.requiredJurisdictionChangeMayChangeQueryProjectionIsTrue boundary

irrelevantCoordinatesDoNotReopen :
  Impact.unrequiredWorldCoordinateChangeReopensResearch boundary ≡ false
irrelevantCoordinatesDoNotReopen =
  Impact.unrequiredWorldCoordinateChangeReopensResearchIsFalse boundary
