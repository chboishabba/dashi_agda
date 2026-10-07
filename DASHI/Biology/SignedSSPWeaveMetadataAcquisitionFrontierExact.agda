module DASHI.Biology.SignedSSPWeaveMetadataAcquisitionFrontierExact where

------------------------------------------------------------------------
-- METADATA-DYNAMICS ACQUISITION FRONTIER FOR THE FULL SIGNED WEAVE GRAPH
--
-- Existing nearby owners now pay more of the rich-state metadata policy:
--   * legacy FRACTRAN prime transport preserves the 3/6/9 address;
--   * successful legacy prime transport records fromPositive residual approach;
--   * generic weave program/execution/normal-form lengths are mechanically
--     derived by SignedSSPWeaveDerivedLengthDynamicsExact.
--
-- What remains genuinely external is therefore only:
--   * the address update semantics of general weave instructions/refineAt369;
--   * the zero-residual-direction update semantics of general instructions;
--   * residual-witness-length dynamics.
-- No map between the legacy four-rule machine and the general weave language is
-- invented here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Biology.FRACTRANSSPTransitionExact as Legacy
import DASHI.Biology.SelfIndexingHyperfabricTetrationExact as Hyper
import DASHI.Biology.SignedSSPWeaveRichMetadataCompilerExact as Compiler
import DASHI.Biology.SignedSSPWeaveDerivedLengthDynamicsExact as Derived
import DASHI.Biology.OrientedZeroWaveTransitionExact as Zero

legacyCanonicalAddressTransportPaid :
  Legacy.address369 Legacy.thirdCanonicalTransfer
  ≡ Legacy.canonicalSSPAddress
legacyCanonicalAddressTransportPaid =
  Legacy.sspAddressIsPreservedByPrimeTransport

legacyResidualTransportToPositivePaid :
  Legacy.zeroApproachResidual
    (Legacy.applyRule Legacy.residual53To47
      (Legacy.primeValuationState
        0 1 0 0
        Legacy.canonicalSSPAddress
        Zero.fromNegative))
  ≡ Zero.fromPositive
legacyResidualTransportToPositivePaid = refl

canonicalVirtualExecutionLengthRecovered :
  Derived.programExecutionCost Signed.canonicalVirtualFiftyThreeProgram ≡ 3
canonicalVirtualExecutionLengthRecovered =
  Derived.canonicalVirtualExecutionCostIsThree

canonicalGeometryExecutionLengthRecovered :
  Derived.programExecutionCost Signed.canonicalGeometricFiftyThreeProgram ≡ 54
canonicalGeometryExecutionLengthRecovered =
  Derived.canonicalGeometryExecutionCostIsFiftyFour

existingComplexityCarrier : Set
existingComplexityCarrier = Hyper.WeaveComplexity

residualMetadataDynamicsSocket : Set₁
residualMetadataDynamicsSocket = Derived.ResidualMetadataDynamics

fullMetadataDynamicsCompiler :
  Derived.ResidualMetadataDynamics → Compiler.RichMetadataDynamics
fullMetadataDynamicsCompiler = Derived.compileRichMetadataDynamics

record SignedSSPWeaveMetadataAcquisitionBoundary : Set where
  constructor signed-ssp-weave-metadata-acquisition-boundary
  field
    legacyAddressPreservationPolicyLocated : Bool
    legacyResidualDirectionPolicyLocated : Bool
    typedComplexityCarrierLocated : Bool
    genericProgramLengthDynamicsPaid : Bool
    genericExecutionLengthDynamicsPaid : Bool
    genericNormalFormLengthDynamicsPaid : Bool
    generalWeaveInstructionToLegacyRuleMapLocated : Bool
    refineAt369AddressDynamicsLocated : Bool
    generalZeroResidualDynamicsLocated : Bool
    residualWitnessLengthDynamicsLocated : Bool
    fullRichMetadataDynamicsRecovered : Bool

canonicalSignedSSPWeaveMetadataAcquisitionBoundary :
  SignedSSPWeaveMetadataAcquisitionBoundary
canonicalSignedSSPWeaveMetadataAcquisitionBoundary =
  signed-ssp-weave-metadata-acquisition-boundary
    true true true
    true true true
    false false false false false
