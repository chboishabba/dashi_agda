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
--     -> active CMP122 Section-2 FORM witness
--     -> least-privilege active regular-E/localization witness
--     -> CMP109/CMP116 literal effective-action continuation.
--
-- The full CMP122 Theorem-1 witness remains a compatibility producer, but the
-- BC1-facing route consumes only preservation of the Sect.-2 form. Quantitative
-- Sect.-2 bounds are therefore not primitive dependencies of this continuation.
--
-- This root does NOT manufacture the published source witness or the literal
-- CMP119 predicate instantiation. Those source-facing payments remain explicit.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.Balaban1989ActiveScaleTheorem1BetaBridgeExact as Active
import DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact as R246
import DASHI.Physics.YangMills.BalabanTheorem1RegularEContinuationRound247Exact as R247

activeScaleCouplingHypothesisCompilerLevel : ProofLevel
activeScaleCouplingHypothesisCompilerLevel =
  R246.activeScaleCouplingHypothesisCompilerLevel

activeSection2FormProjectionCompilerLevel : ProofLevel
activeSection2FormProjectionCompilerLevel =
  Active.activeScaleCMP122Section2FormProjectionLevel

activeRegularESection2PredicateCompilerLevel : ProofLevel
activeRegularESection2PredicateCompilerLevel =
  R246.activeRegularESection2PredicateCompilerLevel

activeRegularESection2FormWitnessCompilerLevel : ProofLevel
activeRegularESection2FormWitnessCompilerLevel =
  R246.activeRegularESection2FormWitnessCompilerLevel

activeTheorem1SourceLevel : ProofLevel
activeTheorem1SourceLevel = Active.activeScaleCMP122Theorem1SourceLevel

activeRegularEContinuationCompilerLevel : ProofLevel
activeRegularEContinuationCompilerLevel =
  R247.activeTheorem1RegularEContinuationCompilerLevel

activeRegularEFormWitnessContinuationCompilerLevel : ProofLevel
activeRegularEFormWitnessContinuationCompilerLevel =
  R247.activeRegularEFormWitnessContinuationCompilerLevel

-- Compatibility source/repository payment. The validator deliberately
-- preserves this as conditional rather than confusing imported bibliographic
-- authority with a theorem-bearing in-repo inhabitant of the exact predicate.
literalActiveCMP119RegularESection2PredicateInstantiationLevel : ProofLevel
literalActiveCMP119RegularESection2PredicateInstantiationLevel =
  R247.literalActiveCMP119RegularESection2PredicateInstantiationLevel

-- Preferred least-privilege payment after projection: downstream BC1 consumes
-- only the active regular-E/localization form witness, not independent Sect.-2
-- quantitative bounds.
literalActiveCMP119RegularESection2FormWitnessLevel : ProofLevel
literalActiveCMP119RegularESection2FormWitnessLevel =
  R247.literalActiveCMP119RegularESection2FormWitnessLevel
