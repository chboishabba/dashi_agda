{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalTraceEntropyBudgetExact where

open import Agda.Builtin.Bool using (Bool; false)

------------------------------------------------------------------------
-- Canonical residual owner for the historical R429 trace/entropy budget lane.
-- Exact compiler/algebra structure is kept distinct from quantitative analytic
-- payment and from source/measure/trace same-object attachment.
------------------------------------------------------------------------

record CMP116CanonicalTraceEntropyBudget
    (ExactCompilerStructure
     QuantitativeTraceEntropyBound
     SameObjectTraceAttachment : Set) : Set₁ where
  field
    exactCompilerStructure : ExactCompilerStructure
    quantitativeTraceEntropyBound : QuantitativeTraceEntropyBound
    sameObjectTraceAttachment : SameObjectTraceAttachment

open CMP116CanonicalTraceEntropyBudget public

compilerStructurePaysAnalyticBound : Bool
compilerStructurePaysAnalyticBound = false

analyticBoundPaysSourceAttachment : Bool
analyticBoundPaysSourceAttachment = false
