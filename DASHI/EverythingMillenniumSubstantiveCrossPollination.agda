module DASHI.EverythingMillenniumSubstantiveCrossPollination where

------------------------------------------------------------------------
-- Whole-repository aggregate for the stacked substantive Millennium tranche.
--
-- The preceding wrapper already imports DASHI.Everything and the complete
-- Hurwitz--Hopf--Noether tranche.  This wrapper adds the RH, Hodge, BSD,
-- complexity, Poincare and graded-VOA validation root without mutating the
-- target branch's aggregate before the stacked PRs are merged.
------------------------------------------------------------------------

import DASHI.EverythingHurwitzHopfNoetherCrossPollination
import DASHI.Mathematics.CrossPollination.MillenniumSubstantiveCrossPollinationValidation
