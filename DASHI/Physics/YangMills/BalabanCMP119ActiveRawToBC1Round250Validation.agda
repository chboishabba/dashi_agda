{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119ActiveRawToBC1Round250Validation where

------------------------------------------------------------------------
-- Focused elaboration root for the current finite-history CMP119 -> BC1 spine.
--
-- Preferred source route after R248:
--
--   concrete raw CMP119 predicate family
--     + genuine CMP122 Theorem-1 witness
--     -> identity E-localization decoder                 [compiler]
--     -> active raw Sect.-2 witness                      [compiler]
--     -> active regular-E/localization form             [compiler]
--     -> active CMP109/CMP116 continuation              [compiler]
--     -> BC1 once the remaining physical inputs are paid.
--
-- The legacy opaque-predicate decoder remains available as an alternate route,
-- but it is no longer a primitive dependency of the preferred construction.
-- Remaining theorem-bearing physical/source inputs after representation are:
--
--   * genuine CMP122 Theorem-1 witness on the concrete predicate family;
--   * physical second-variation calculus;
--   * literal CMP109 Eq.(5.1) on the same active continuation;
--   * extraction of the four normalized CMP116 analytic demands.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP119ActiveRawToBC1Round250Exact as R250

activeRawToBC1CompilerLevel : ProofLevel
activeRawToBC1CompilerLevel = R250.activeRawToBC1CompilerLevel

activeRawBC1SameRegularELevel : ProofLevel
activeRawBC1SameRegularELevel = R250.activeRawBC1SameRegularELevel

-- RED surface: Round250 must expose the R248 preferred concrete-predicate route
-- as a first-class compiler, rather than leaving decoder/rawWitness as primitive.
preferredConcreteActiveRawToBC1CompilerLevel : ProofLevel
preferredConcreteActiveRawToBC1CompilerLevel =
  R250.preferredConcreteActiveRawToBC1CompilerLevel

preferredConcreteCMP122SourceWitnessLevel : ProofLevel
preferredConcreteCMP122SourceWitnessLevel =
  R250.preferredConcreteCMP122SourceWitnessLevel

-- Legacy alternate route retained for archaeology/compatibility.
literalRawELocalizedAnalyticDecoderLevel : ProofLevel
literalRawELocalizedAnalyticDecoderLevel =
  R250.literalRawELocalizedAnalyticDecoderLevel

physicalSecondVariationLinearityLevel : ProofLevel
physicalSecondVariationLinearityLevel =
  R250.physicalSecondVariationLinearityLevel

literalCMP109Equation51OnActiveRegularELevel : ProofLevel
literalCMP109Equation51OnActiveRegularELevel =
  R250.literalCMP109Equation51OnActiveRegularELevel

literalCMP116FiniteNormalizedDemandExtractionLevel : ProofLevel
literalCMP116FiniteNormalizedDemandExtractionLevel =
  R250.literalCMP116FiniteNormalizedDemandExtractionLevel
