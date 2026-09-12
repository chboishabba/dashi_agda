{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RegularEActiveRound247Validation where

------------------------------------------------------------------------
-- Focused validation root for the preferred finite-active CMP119/CMP122 ->
-- CMP109/CMP116 continuation.
--
-- Importing this module forces elaboration of the exact path:
--
--   finite-mode beta history
--     -> raw CMP119 selected E_k on that SAME history
--     -> active CMP122 Sect.-2 witness
--     -> explicit decoder of opaque ELocalizedAnalytic(k,E_k)
--     -> concrete active regular-E/localization form witness
--     -> CMP109/CMP116 literal effective-action continuation.
--
-- The full CMP122 Theorem-1 witness remains a compatibility producer, but the
-- BC1-facing route consumes only preservation of the Sect.-2 form. Quantitative
-- Sect.-2 bounds are therefore not primitive dependencies of this continuation.
--
-- This root does NOT manufacture the literal decoder. Source authority that
-- E_k is localized/analytic is distinct from the repository realization of its
-- concrete components/activity/sum equality, so that payment remains explicit.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.Balaban1989ActiveScaleTheorem1BetaBridgeExact as Active
import DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact as R246
import DASHI.Physics.YangMills.BalabanTheorem1RegularEContinuationRound247Exact as R247
import DASHI.Physics.YangMills.BalabanCMP119RawActiveRegularEDecoderRound248Exact as R248

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

rawActiveRegularEDecoderCompilerLevel : ProofLevel
rawActiveRegularEDecoderCompilerLevel =
  R248.rawActiveRegularEDecoderCompilerLevel

rawActiveRegularEFormWitnessCompilerLevel : ProofLevel
rawActiveRegularEFormWitnessCompilerLevel =
  R248.rawActiveRegularEFormWitnessCompilerLevel

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

-- Preferred first source/repository payment after the R248 recut: interpret the
-- opaque CMP119 Sect.-2 E-localization predicate as concrete localization data
-- for the exact raw function-valued E_k on the finite history.
literalRawELocalizedAnalyticDecoderLevel : ProofLevel
literalRawELocalizedAnalyticDecoderLevel =
  R248.literalRawELocalizedAnalyticDecoderLevel

-- Downstream BC1 consumes only the projected active regular-E/localization form
-- witness; independent quantitative Sect.-2 bounds remain out of this cut.
literalActiveCMP119RegularESection2FormWitnessLevel : ProofLevel
literalActiveCMP119RegularESection2FormWitnessLevel =
  R247.literalActiveCMP119RegularESection2FormWitnessLevel
