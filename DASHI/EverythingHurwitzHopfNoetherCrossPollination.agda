module DASHI.EverythingHurwitzHopfNoetherCrossPollination where

------------------------------------------------------------------------
-- Whole-repository aggregate for the stacked Hurwitz--Hopf--Noether tranche.
--
-- DASHI.Everything remains owned by the target branch.  This wrapper imports
-- that complete aggregate and then the cumulative cross-pollination root, so
-- the exact PR head can be checked against the full repository without
-- silently editing the base branch's aggregate before its Round Thirty work is
-- merged.
------------------------------------------------------------------------

import DASHI.Everything
import DASHI.Mathematics.CrossPollination.HurwitzHopfNoetherMillenniumCrossPollinationValidation
