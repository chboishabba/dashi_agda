module DASHI.Physics.Closure.NSTriadKNUpperShellCollarRemoteSplitRegression where

------------------------------------------------------------------------
-- RED regression for S2b2 collar/remote decomposition.
--
-- The production owner must split the SAME literal upper-shell R98 packet:
--
--   F_{>=j} = F_{=j} + F_{>=j+1}
--
-- without changing selector geometry or introducing an estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNUpperShellCollarRemoteSplitExact as Split

collarRemoteSelectorSplitClosedIsTrue :
  Split.collarRemoteSelectorSplitClosed ≡ true
collarRemoteSelectorSplitClosedIsTrue =
  Split.collarRemoteSelectorSplitClosedIsTrue

collarRemoteBoundaryFluxSplitClosedIsTrue :
  Split.collarRemoteBoundaryFluxSplitClosed ≡ true
collarRemoteBoundaryFluxSplitClosedIsTrue =
  Split.collarRemoteBoundaryFluxSplitClosedIsTrue

s2b2QuantitativeEstimateStillOpenIsTrue :
  Split.s2b2QuantitativeEstimateStillOpen ≡ true
s2b2QuantitativeEstimateStillOpenIsTrue =
  Split.s2b2QuantitativeEstimateStillOpenIsTrue
