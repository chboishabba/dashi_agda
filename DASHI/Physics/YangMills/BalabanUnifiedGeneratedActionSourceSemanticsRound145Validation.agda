{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionSourceSemanticsRound145Validation where

------------------------------------------------------------------------
-- Focused Round145 validation surface.
--
-- The important regression is theorem-valued: the old Round132 consumer admits
-- a constant density interpretation, whereas the strengthened consumer is
-- indexed by a fixed source semantics before the BC1 equality is supplied.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionSourceSemanticsRound145Exact

round145ConstantMapAuditPresent = round132ConstantRepresentationAuditLevel
round145SourceSemanticCompilerPresent = sourceSemanticRound132CompilerLevel
round145LiteralDensitySemanticsStillSourceOpen =
  literalCMP122EffectiveDensitySemanticsRound145Level
round145LiteralSelectedSameActionStillSourceOpen =
  literalSelectedCMP122DensityIsBC1GeneratedActionRound145Level
