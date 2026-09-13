{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.YMActiveRawM1M2MassGapFullSpineValidation where

------------------------------------------------------------------------
-- Validation root for the current mandatory mass-gap residual after theorem-
-- facing M1 and M2 payments.
--
-- Remaining mandatory coordinates:
--   M3, M4, M6, M7a, M7b, M7c, M8, M9.
--
-- M5 remains optional for sharp edge identification.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Closure.YMActiveRawMassGapFullSpineValidation as Base
import DASHI.Physics.Closure.YMPhysicalScaleM1GateAdapterExact as M1
import DASHI.Physics.Closure.YMActiveRawDenseCoreM2GateAdapterExact as M2
import DASHI.Physics.Closure.YMActiveRawM1M2MassGapResidualCompilerExact as Residual

activeRawToBC1CompilerLevel : ProofLevel
activeRawToBC1CompilerLevel = Base.activeRawToBC1CompilerLevel

activeRawBC1ToDenseCoreCompilerLevel : ProofLevel
activeRawBC1ToDenseCoreCompilerLevel = Base.activeRawBC1ToDenseCoreCompilerLevel

physicalScaleM1TransportCompilerLevel : ProofLevel
physicalScaleM1TransportCompilerLevel = M1.physicalScaleM1TransportCompilerLevel

activeRawDenseCoreM2TransportCompilerLevel : ProofLevel
activeRawDenseCoreM2TransportCompilerLevel =
  M2.activeRawDenseCoreM2TransportCompilerLevel

activeRawM1M2ToMandatoryGateCompilerLevel : ProofLevel
activeRawM1M2ToMandatoryGateCompilerLevel =
  Residual.activeRawM1M2ToMandatoryGateCompilerLevel

uniformPhysicalMassScaleBridgeInputLevel : ProofLevel
uniformPhysicalMassScaleBridgeInputLevel =
  M1.uniformPhysicalMassScaleBridgeInputLevel

physicalScaleM1SamePropositionWeldLevel : ProofLevel
physicalScaleM1SamePropositionWeldLevel =
  M1.physicalScaleM1SamePropositionWeldLevel

activeRawDenseCoreM2SamePropositionWeldLevel : ProofLevel
activeRawDenseCoreM2SamePropositionWeldLevel =
  M2.activeRawDenseCoreM2SamePropositionWeldLevel

remainingMandatoryMassGapGatesAfterM1M2Level : ProofLevel
remainingMandatoryMassGapGatesAfterM1M2Level =
  Residual.remainingMandatoryMassGapGatesAfterM1M2Level
