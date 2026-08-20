module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound84Validation where

------------------------------------------------------------------------
-- ROUND84 FOCUSED VALIDATION ROOT
--
-- Import the established Round61 integration surface first, then the current
-- shortest Clay-facing six-lemma cutset.  A successful Agda check of THIS module
-- therefore forces typechecking of the new Round83/84 theorem-producing tranche
-- without rewriting the large historical Round61 validation file.
--
-- This is a kernel-target convenience only.  Import success would establish
-- source/type correctness of the formal compilers; it would not inhabit any of
-- the six remaining conditional physical analytic theorem families.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound61DLRTransferAuditValidation
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound84SixAnalyticLemmaExact
