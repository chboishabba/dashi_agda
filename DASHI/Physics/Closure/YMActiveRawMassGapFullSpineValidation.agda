{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.YMActiveRawMassGapFullSpineValidation where

------------------------------------------------------------------------
-- Focused validation root for the current continuous YM proof spine:
--
-- raw CMP119 E_k
--   -> active BC1
--   -> Row C
--   -> dense-core spectral exclusion
--   -> exact M2 gate payment
--   -> mandatory-gate residual M1/M3/M4/M6/M7a/b/c/M8/M9.
--
-- This root intentionally does not manufacture any physical source, Row-C,
-- continuum, Hamiltonian or reconstruction witness.  It only forces elaboration
-- of the compilers that connect those theorem-bearing inputs.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP119ActiveRawToBC1Round250Exact as R250
import DASHI.Physics.Closure.YMActiveRawBC1ToDenseCoreProofSpineExact as DenseSpine
import DASHI.Physics.Closure.YMActiveRawDenseCoreM2GateAdapterExact as M2
import DASHI.Physics.Closure.YMActiveRawMassGapGateResidualCompilerExact as Residual

activeRawToBC1CompilerLevel : ProofLevel
activeRawToBC1CompilerLevel = R250.activeRawToBC1CompilerLevel

activeRawBC1ToDenseCoreCompilerLevel : ProofLevel
activeRawBC1ToDenseCoreCompilerLevel =
  DenseSpine.activeRawBC1ToDenseCoreCompilerLevel

activeRawDenseCoreM2TransportCompilerLevel : ProofLevel
activeRawDenseCoreM2TransportCompilerLevel =
  M2.activeRawDenseCoreM2TransportCompilerLevel

activeRawM2ToMandatoryGateCompilerLevel : ProofLevel
activeRawM2ToMandatoryGateCompilerLevel =
  Residual.activeRawM2ToMandatoryGateCompilerLevel

-- Finite source / analytic payments.
literalRawELocalizedAnalyticDecoderLevel : ProofLevel
literalRawELocalizedAnalyticDecoderLevel =
  DenseSpine.literalRawELocalizedAnalyticDecoderLevel

physicalSecondVariationLinearityLevel : ProofLevel
physicalSecondVariationLinearityLevel =
  DenseSpine.physicalSecondVariationLinearityLevel

literalCMP109Equation51OnActiveRegularELevel : ProofLevel
literalCMP109Equation51OnActiveRegularELevel =
  DenseSpine.literalCMP109Equation51OnActiveRegularELevel

literalCMP116FiniteNormalizedDemandExtractionLevel : ProofLevel
literalCMP116FiniteNormalizedDemandExtractionLevel =
  DenseSpine.literalCMP116FiniteNormalizedDemandExtractionLevel

-- Row-C / continuum payments.
rowCPostBC2PhysicalCompletionLevel : ProofLevel
rowCPostBC2PhysicalCompletionLevel =
  DenseSpine.rowCPostBC2PhysicalCompletionLevel

physicalDenseCoreProjectionDataLevel : ProofLevel
physicalDenseCoreProjectionDataLevel =
  DenseSpine.physicalDenseCoreProjectionDataLevel

rowCToDenseCoreSameObjectWeldLevel : ProofLevel
rowCToDenseCoreSameObjectWeldLevel =
  DenseSpine.rowCToDenseCoreSameObjectWeldLevel

activeRawDenseCoreM2SamePropositionWeldLevel : ProofLevel
activeRawDenseCoreM2SamePropositionWeldLevel =
  M2.activeRawDenseCoreM2SamePropositionWeldLevel

remainingMandatoryMassGapGatesAfterM2Level : ProofLevel
remainingMandatoryMassGapGatesAfterM2Level =
  Residual.remainingMandatoryMassGapGatesAfterM2Level
