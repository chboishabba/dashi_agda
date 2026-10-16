module DASHI.Biology.SignedSSPWeaveMetadataAcquisitionFrontierExact where

------------------------------------------------------------------------
-- METADATA-DYNAMICS ACQUISITION FRONTIER FOR THE FULL SIGNED WEAVE GRAPH
--
-- Existing nearby owners pay:
--   * legacy FRACTRAN prime transport preserves the 3/6/9 address;
--   * successful legacy prime transport records fromPositive residual approach;
--   * generic weave program/execution/normal-form lengths are mechanically
--     derived by SignedSSPWeaveDerivedLengthDynamicsExact;
--   * every general weave instruction EXCEPT refineAt369 is proved
--     refinement-neutral by executable WeaveEffect semantics, giving the
--     conservative identity action on an already supplied 3/6/9 address.
--
-- The refineAt369 seam is now sharper than "missing source semantics".  The
-- current rich metadata carrier is literally Address 3 and the dynamics socket
-- is Address 3 -> Address 3, so ANY current step is definitionally depth
-- preserving.  In addition, refineAt369 is nullary and carries no child digit.
-- Thus, if refineAt369 is intended as literal prefix/tree refinement, the
-- current interface is structurally incapable of expressing it.  The new
-- fixed-depth no-go owner constructs the minimal variable-depth + explicit
-- Digit369 child repair without promoting that repair to scientific semantics.
--
-- Remaining external/design payments are therefore:
--   * decide whether refineAt369 is same-depth mutation or true depth refinement;
--   * if true refinement, migrate the rich carrier/compiler to the typed
--     variable-depth repair and source the child-selection law;
--   * source zero-residual-direction updates for general instructions;
--   * source residual-witness-length dynamics.
-- No legacy/general instruction map or semantic child selection is invented.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Biology.FRACTRANSSPTransitionExact as Legacy
import DASHI.Biology.SelfIndexingHyperfabricTetrationExact as Hyper
import DASHI.Biology.SignedSSPWeaveRichMetadataCompilerExact as Compiler
import DASHI.Biology.SignedSSPWeaveDerivedLengthDynamicsExact as Derived
import DASHI.Biology.SignedSSPWeaveAddressNeutralDynamicsExact as Neutral
import DASHI.Biology.SignedSSPWeaveRefineAt369FixedDepthNoGoExact as RefineNoGo
import DASHI.Biology.OrientedZeroWaveTransitionExact as Zero
import DASHI.Geometry.SSP369Ultrametric as SSP

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

nonRefinementAddressDynamicsPaid : Bool
nonRefinementAddressDynamicsPaid = true

refineAt369AddressDynamicsStillOpen :
  Neutral.refineAt369AddressDynamicsPaid Neutral.canonicalAddressDynamicsMaxCut
  ≡ false
refineAt369AddressDynamicsStillOpen = refl

fixedDepthRichStepCannotIncreaseDepth :
  (step : SSP.Address 3 → SSP.Address 3) →
  (address : SSP.Address 3) →
  SSP.addressDepth (step address) ≡ SSP.addressDepth address
fixedDepthRichStepCannotIncreaseDepth =
  RefineNoGo.fixedDepthThreeStepPreservesAddressDepth

record SignedSSPWeaveMetadataAcquisitionBoundary : Set where
  constructor signed-ssp-weave-metadata-acquisition-boundary
  field
    legacyAddressPreservationPolicyLocated : Bool
    legacyResidualDirectionPolicyLocated : Bool
    typedComplexityCarrierLocated : Bool
    genericProgramLengthDynamicsPaid : Bool
    genericExecutionLengthDynamicsPaid : Bool
    genericNormalFormLengthDynamicsPaid : Bool
    nonRefinementInstructionAddressDynamicsPaid : Bool
    fixedDepthAddressRefinementNoGoPaid : Bool
    variableDepthExplicitChildRepairConstructed : Bool
    currentRefineInstructionCarriesChildChoice : Bool
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
    true
    true true false
    false false false false false
