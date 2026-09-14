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
--     -> concrete same-E Sect.-2 predicate vocabulary
--     -> active CMP122 theorem witness on that vocabulary
--     -> R248 active regular-E/localization form witness [compiler]
--     -> CMP109/CMP116 literal effective-action continuation.
--
-- The running-coupling weld is definitional in the raw finite-history state.
-- The preferred E-localization decoder is identity by construction.  Therefore
-- neither is a primitive source payment on the shortest BC1 path.
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

preferredConcreteELocalizationPredicateCompilerLevel : ProofLevel
preferredConcreteELocalizationPredicateCompilerLevel =
  R248.preferredConcreteELocalizationPredicateCompilerLevel

preferredConcreteELocalizationIdentityDecoderCompilerLevel : ProofLevel
preferredConcreteELocalizationIdentityDecoderCompilerLevel =
  R248.preferredConcreteELocalizationIdentityDecoderCompilerLevel

-- New least-privilege route: the finite-history coupling identity and concrete
-- E-localization decoder are both compiler-owned.  A genuine CMP122 theorem
-- witness on the concrete predicate compiles directly to the R246 form witness.
preferredConcreteActiveRegularEFormFromTheorem1CompilerLevel : ProofLevel
preferredConcreteActiveRegularEFormFromTheorem1CompilerLevel =
  R248.preferredConcreteActiveRegularEFormFromTheorem1CompilerLevel

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

-- Legacy opaque-predicate route: an explicit decoder is still conditional.
literalRawELocalizedAnalyticDecoderLevel : ProofLevel
literalRawELocalizedAnalyticDecoderLevel =
  R248.literalRawELocalizedAnalyticDecoderLevel

-- Preferred source payment: the concrete E-localization predicate is already
-- the repository data shape and coupling is already the finite-history coupling.
-- The remaining primitive source input is therefore the CMP122 theorem witness
-- instantiated on this exact concrete predicate family.
literalCMP122Theorem1OnConcreteELocalizationPredicateLevel : ProofLevel
literalCMP122Theorem1OnConcreteELocalizationPredicateLevel =
  R248.literalCMP122Theorem1OnConcreteELocalizationPredicateLevel

-- The resulting active Sect.-2 witness/form is downstream compiler output.
literalConcreteELocalizationActiveSection2WitnessLevel : ProofLevel
literalConcreteELocalizationActiveSection2WitnessLevel =
  R248.literalConcreteELocalizationActiveSection2WitnessLevel

-- Optional reuse decomposition from R249.  The older function-valued
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
