{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayMassGapSemanticMaxCutRound503Exact where

------------------------------------------------------------------------
-- GOAL-1 B / ROUND503: LITERAL MASS-GAP SEMANTIC MAX-CUT
--
-- The quantitative/spectral gap mathematics is upstream.  R458 packages five
-- opaque Clay endpoint predicates.  Since the semantics interface deliberately
-- supplies no implication among them, an exact residual max-cut must expose all
-- five rather than hiding them under one conditional label.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayGoal1MassGapSemanticAttachmentRound458Exact as R458

round503T2SemanticCompilerLevel : ProofLevel
round503T2SemanticCompilerLevel =
  R458.round458T2SemanticCompilerLevel

literalRound503VacuumSectorPositiveEnergySemanticsLevel : ProofLevel
literalRound503VacuumSectorPositiveEnergySemanticsLevel = conditional

literalRound503StrictPositiveMassGapSemanticsLevel : ProofLevel
literalRound503StrictPositiveMassGapSemanticsLevel = conditional

literalRound503PhysicalScaleLowerBoundSemanticsLevel : ProofLevel
literalRound503PhysicalScaleLowerBoundSemanticsLevel = conditional

literalRound503NoSpectralPollutionSemanticsLevel : ProofLevel
literalRound503NoSpectralPollutionSemanticsLevel = conditional

literalRound503GapAndClusteringDerivedSemanticsLevel : ProofLevel
literalRound503GapAndClusteringDerivedSemanticsLevel = conditional
