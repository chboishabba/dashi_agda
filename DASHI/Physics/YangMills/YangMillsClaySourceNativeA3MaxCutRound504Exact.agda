{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClaySourceNativeA3MaxCutRound504Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND504: SOURCE-NATIVE CONTINUUM/OS MAX-CUT
--
-- R457/R128 package four distinct physical/source meanings:
--
--   S1 selected stress-generating density is the literal finite YM family;
--   S2 that literal finite family has the declared literal continuum limit;
--   S3 the declared literal Schwinger family belongs to that continuum;
--   S4 the source OS Schwinger system is that SAME literal Schwinger family.
--
-- R128's same-family transport is compiler-owned after these payments.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanLiteralFiniteMeasureStressLaneRound125Exact as R125
import DASHI.Physics.YangMills.BalabanLiteralSchwingerStressRecoveryRound126Exact as R126
import DASHI.Physics.YangMills.BalabanOSLiteralSchwingerWeldRound127Exact as R127
import DASHI.Physics.YangMills.BalabanSameFamilyOSStressRecoveryRound128Exact as R128

round504SameFamilyRecoveryCompilerLevel : ProofLevel
round504SameFamilyRecoveryCompilerLevel =
  R128.sameFamilyOSStressRecoveryCompilerLevel

literalRound504StressDensityIsLiteralFiniteMeasureLevel : ProofLevel
literalRound504StressDensityIsLiteralFiniteMeasureLevel =
  R125.literalBalabanStressDensityIsClayFiniteMeasureLevel

-- R126 historically gives one aggregate label for S2+S3.  The record exposes
-- them as independent endpoint predicates, so the exact max-cut keeps them
-- separately visible.
literalRound504FiniteFamilyContinuumLimitLevel : ProofLevel
literalRound504FiniteFamilyContinuumLimitLevel = conditional

literalRound504LiteralSchwingerBelongsLevel : ProofLevel
literalRound504LiteralSchwingerBelongsLevel = conditional

literalRound504SourceOSIsLiteralSchwingerLevel : ProofLevel
literalRound504SourceOSIsLiteralSchwingerLevel =
  R127.literalBalabanOSSystemIsClaySchwingerLevel
