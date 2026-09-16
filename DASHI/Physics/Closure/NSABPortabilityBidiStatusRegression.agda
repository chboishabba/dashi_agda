module DASHI.Physics.Closure.NSABPortabilityBidiStatusRegression where

------------------------------------------------------------------------
-- Regression for the A/B bidirectional portability audit.
--
-- A remains mathematically independent.  This regression requires the live
-- control plane to distinguish reusable analytic structure from torus-only
-- realization and from actually observed whole-space transport.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSABPortabilityBidiStatusExact as Bidi

bToAImplicationBlocked : Bidi.bToAImplicationAllowed ≡ false
bToAImplicationBlocked = Bidi.bToAImplicationAllowedIsFalse

aToBImplicationBlocked : Bidi.aToBImplicationAllowed ≡ false
aToBImplicationBlocked = Bidi.aToBImplicationAllowedIsFalse

bPhaseAnalyticCoreCandidateTracked :
  Bidi.bPhaseAnalyticCoreCandidateTracked ≡ true
bPhaseAnalyticCoreCandidateTracked =
  Bidi.bPhaseAnalyticCoreCandidateTrackedIsTrue

bCommAnalyticCoreCandidateTracked :
  Bidi.bCommAnalyticCoreCandidateTracked ≡ true
bCommAnalyticCoreCandidateTracked =
  Bidi.bCommAnalyticCoreCandidateTrackedIsTrue

torusSpecificRealizationSeparated :
  Bidi.torusSpecificRealizationSeparated ≡ true
torusSpecificRealizationSeparated =
  Bidi.torusSpecificRealizationSeparatedIsTrue

currentS2b2PortabilityFactoredIsTrue :
  Bidi.currentS2b2PortabilityFactored ≡ true
currentS2b2PortabilityFactoredIsTrue =
  Bidi.currentS2b2PortabilityFactoredIsTrue

d1aDampedTangentAnalyticCoreTrackedIsTrue :
  Bidi.d1aDampedTangentAnalyticCoreTracked ≡ true
d1aDampedTangentAnalyticCoreTrackedIsTrue =
  Bidi.d1aDampedTangentAnalyticCoreTrackedIsTrue

d1bWholeSpaceTransportStillOpenIsTrue :
  Bidi.d1bWholeSpaceTransportStillOpen ≡ true
d1bWholeSpaceTransportStillOpenIsTrue =
  Bidi.d1bWholeSpaceTransportStillOpenIsTrue

d1bOrderedKernelCoordinateTrackedIsTrue :
  Bidi.d1bOrderedKernelCoordinateTracked ≡ true
d1bOrderedKernelCoordinateTrackedIsTrue =
  Bidi.d1bOrderedKernelCoordinateTrackedIsTrue

d1b2CoherentCovarianceCoordinateTrackedIsTrue :
  Bidi.d1b2CoherentCovarianceCoordinateTracked ≡ true
d1b2CoherentCovarianceCoordinateTrackedIsTrue =
  Bidi.d1b2CoherentCovarianceCoordinateTrackedIsTrue

wholeSpaceTransportObservedIsFalse :
  Bidi.wholeSpaceTransportObserved ≡ false
wholeSpaceTransportObservedIsFalse =
  Bidi.wholeSpaceTransportObservedIsFalse

aPortabilityAuditActiveIsTrue :
  Bidi.aPortabilityAuditActive ≡ true
aPortabilityAuditActiveIsTrue =
  Bidi.aPortabilityAuditActiveIsTrue
