module DASHI.Physics.Closure.NSABPortabilityBidiStatusRegression where

------------------------------------------------------------------------
-- RED regression for the A/B bidirectional portability audit.
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

wholeSpaceTransportObservedIsFalse :
  Bidi.wholeSpaceTransportObserved ≡ false
wholeSpaceTransportObservedIsFalse =
  Bidi.wholeSpaceTransportObservedIsFalse

aPortabilityAuditActiveIsTrue :
  Bidi.aPortabilityAuditActive ≡ true
aPortabilityAuditActiveIsTrue =
  Bidi.aPortabilityAuditActiveIsTrue
