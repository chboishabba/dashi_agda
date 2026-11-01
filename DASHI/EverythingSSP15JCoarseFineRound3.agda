module DASHI.EverythingSSP15JCoarseFineRound3 where

------------------------------------------------------------------------
-- Authoritative aggregate extension.
--
-- Import the existing repository-wide aggregate unchanged, then add the
-- complete SSP15/nonary/j-coarse-j-fine aggregate.  This avoids rewriting the
-- very large DASHI.Everything import ledger while still making one top-level
-- module typecheck the existing authority surface and the complete new tranche
-- together.
------------------------------------------------------------------------

import DASHI.Everything
import DASHI.Biology.PointedBulkSporadicTarotEverything
import DASHI.Biology.SSP15JCoarseFineRound3Validation
