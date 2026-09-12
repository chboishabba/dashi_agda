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
--     -> R248 exact-E decoder
--     -> optional R249 reuse of the older function-valued localization carrier
--        through an explicit same-E weld (no history coercion)
--     -> concrete active regular-E/localization form witness
--     -> CMP109/CMP116 literal effective-action continuation.
--
-- The full CMP122 Theorem-1 witness remains a compatibility producer, but the
-- BC1-facing route consumes only preservation of the Sect.-2 form. Quantitative
-- Sect.-2 bounds are therefore not primitive dependencies of this continuation.
--
-- Source authority that E_k is localized/analytic is distinct from the concrete
-- repository localization carrier.  R249 reuses that carrier only after proving
-- it is the SAME E_k as the finite-history raw term.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.Balaban1989ActiveScaleTheorem1BetaBridgeExact as Active
import DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact as R246
import DASHI.Physics.YangMills.BalabanTheorem1RegularEContinuationRound247Exact as R247
import DASHI.Physics.YangMills.BalabanCMP119RawActiveRegularEDecoderRound248Exact as R248
import DASHI.Physics.YangMills.BalabanCMP119RegularELocalizationToActiveRawRound249Exact as R249

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

functionalLocalizationToRawDecoderCompilerLevel : ProofLevel
functionalLocalizationToRawDecoderCompilerLevel =
  R249.functionalLocalizationToRawDecoderCompilerLevel

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

-- Direct R248 source/repository payment: interpret the opaque CMP119 Sect.-2
-- E-localization predicate as concrete localization data for the exact raw E_k.
literalRawELocalizedAnalyticDecoderLevel : ProofLevel
literalRawELocalizedAnalyticDecoderLevel =
  R248.literalRawELocalizedAnalyticDecoderLevel

-- Preferred reuse decomposition from R249.  The older function-valued
-- localization carrier may be reused, but only after an explicit same-E weld to
-- the finite-history raw regular term.  Neither payment is manufactured here.
literalFunctionalRegularELocalizationCarrierLevel : ProofLevel
literalFunctionalRegularELocalizationCarrierLevel =
  R249.literalFunctionalRegularELocalizationCarrierLevel

literalFunctionalToActiveRawRegularEWeldLevel : ProofLevel
literalFunctionalToActiveRawRegularEWeldLevel =
  R249.literalFunctionalToActiveRawRegularEWeldLevel

-- Downstream BC1 consumes only the projected active regular-E/localization form
-- witness; independent quantitative Sect.-2 bounds remain out of this cut.
literalActiveCMP119RegularESection2FormWitnessLevel : ProofLevel
literalActiveCMP119RegularESection2FormWitnessLevel =
  R247.literalActiveCMP119RegularESection2FormWitnessLevel
