{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.YMActiveRawBC1ToDenseCoreProofSpineValidation where

------------------------------------------------------------------------
-- Focused elaboration root for the current continuous YM proof spine:
--
--   finite-history raw CMP119 E_k
--     -> active BC1 differentiated carrier
--     -> Row-C geometric clustering
--     -> dense-core spectral exclusion.
--
-- Compiler closure is separated from physical/source inputs.  This validation
-- root deliberately keeps all remaining finite, Row-C and continuum payments
-- conditional rather than treating the composition itself as a mass-gap proof.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.YMActiveRawBC1ToDenseCoreProofSpineExact as Spine

activeRawBC1ToDenseCoreCompilerLevel : ProofLevel
activeRawBC1ToDenseCoreCompilerLevel =
  Spine.activeRawBC1ToDenseCoreCompilerLevel

literalRawELocalizedAnalyticDecoderLevel : ProofLevel
literalRawELocalizedAnalyticDecoderLevel =
  Spine.literalRawELocalizedAnalyticDecoderLevel

physicalSecondVariationLinearityLevel : ProofLevel
physicalSecondVariationLinearityLevel =
  Spine.physicalSecondVariationLinearityLevel

literalCMP109Equation51OnActiveRegularELevel : ProofLevel
literalCMP109Equation51OnActiveRegularELevel =
  Spine.literalCMP109Equation51OnActiveRegularELevel

literalCMP116FiniteNormalizedDemandExtractionLevel : ProofLevel
literalCMP116FiniteNormalizedDemandExtractionLevel =
  Spine.literalCMP116FiniteNormalizedDemandExtractionLevel

rowCPostBC2PhysicalCompletionLevel : ProofLevel
rowCPostBC2PhysicalCompletionLevel =
  Spine.rowCPostBC2PhysicalCompletionLevel

physicalDenseCoreProjectionDataLevel : ProofLevel
physicalDenseCoreProjectionDataLevel =
  Spine.physicalDenseCoreProjectionDataLevel

rowCToDenseCoreSameObjectWeldLevel : ProofLevel
rowCToDenseCoreSameObjectWeldLevel =
  Spine.rowCToDenseCoreSameObjectWeldLevel
