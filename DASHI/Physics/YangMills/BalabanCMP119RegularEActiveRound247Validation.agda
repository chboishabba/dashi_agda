{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RegularEActiveRound247Validation where

------------------------------------------------------------------------
-- Focused validation root for the preferred finite-active CMP119/CMP122 ->
-- CMP109/CMP116 continuation.
--
-- Importing this module forces elaboration of the exact path:
--
--   finite-mode beta history
--     -> ActiveScale coupling hypothesis
--     -> consumer-indexed CMP119 regular-E Section-2 predicate
--     -> active CMP122 Theorem-1 witness
--     -> function-valued E_k + localized composite-sum representation
--     -> CMP109/CMP116 literal effective-action continuation.
--
-- This root does NOT manufacture the published Theorem-1 witness or the
-- literal CMP119 predicate instantiation.  Those source-facing payments remain
-- explicit.  Its purpose is only to ensure the preferred active-scale compiler
-- path elaborates as one focused contract instead of silently falling back to
-- the legacy all-Nat wrapper.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.Balaban1989ActiveScaleTheorem1BetaBridgeExact as Active
import DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact as R246
import DASHI.Physics.YangMills.BalabanTheorem1RegularEContinuationRound247Exact as R247

activeScaleCouplingHypothesisCompilerLevel : ProofLevel
activeScaleCouplingHypothesisCompilerLevel =
  R246.activeScaleCouplingHypothesisCompilerLevel

activeRegularESection2PredicateCompilerLevel : ProofLevel
activeRegularESection2PredicateCompilerLevel =
  R246.activeRegularESection2PredicateCompilerLevel

activeTheorem1SourceLevel : ProofLevel
activeTheorem1SourceLevel = Active.activeScaleCMP122Theorem1SourceLevel

activeRegularEContinuationCompilerLevel : ProofLevel
activeRegularEContinuationCompilerLevel =
  R247.activeTheorem1RegularEContinuationCompilerLevel

-- Surviving source/repository payment.  The validator deliberately preserves
-- this as conditional rather than confusing imported bibliographic authority
-- with a theorem-bearing in-repo inhabitant of the exact active predicate.
literalActiveCMP119RegularESection2PredicateInstantiationLevel : ProofLevel
literalActiveCMP119RegularESection2PredicateInstantiationLevel =
  R247.literalActiveCMP119RegularESection2PredicateInstantiationLevel
