{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalTraceEntropyBudgetExact where

open import Agda.Builtin.Bool using (Bool; false)

------------------------------------------------------------------------
-- Canonical residual owner for the historical CMP116/R429 trace/entropy lane.
--
-- PRIMARY SOURCE
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- SOURCE BOUNDARY / DASHI EXTENSION
-- Historical Round work proves the exact finite entropy/compiler arithmetic
-- (including the 8^d × 16^-d -> 2^-d payment) relative to its source-facing
-- carriers.  This canonical parameterization is a DASHI EXTENSION separating
-- that compiler structure from the remaining quantitative source bound and
-- same-object trace/source attachment.
--
-- The selected source, trace, compiler value and both predicates are external
-- parameters.  The residual constructor can only provide evidence for those
-- already-fixed predicates; it cannot choose them to make the debt vacuous.
------------------------------------------------------------------------

record CMP116CanonicalTraceEntropyBudget
    (SelectedSource : Set)
    (selectedSource : SelectedSource)
    (TraceCarrier : Set)
    (selectedTrace : TraceCarrier)
    (ExactCompilerStructure : Set)
    (exactCompilerStructure : ExactCompilerStructure)
    (QuantitativeTraceEntropyBound : ExactCompilerStructure → TraceCarrier → Set)
    (SameObjectTraceAttachment : SelectedSource → TraceCarrier → Set) : Set₁ where
  field
    quantitativeTraceEntropyBound :
      QuantitativeTraceEntropyBound exactCompilerStructure selectedTrace

    sameObjectTraceAttachment :
      SameObjectTraceAttachment selectedSource selectedTrace

------------------------------------------------------------------------

open CMP116CanonicalTraceEntropyBudget public

compilerStructurePaysAnalyticBound : Bool
compilerStructurePaysAnalyticBound = false

analyticBoundPaysSourceAttachment : Bool
analyticBoundPaysSourceAttachment = false

clayPromotion : Bool
clayPromotion = false
