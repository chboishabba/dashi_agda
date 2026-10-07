module DASHI.Biology.SignedSSPWeaveMetadataAcquisitionFrontierExact where

------------------------------------------------------------------------
-- METADATA-DYNAMICS ACQUISITION FRONTIER FOR THE FULL SIGNED WEAVE GRAPH
--
-- Existing nearby owners do contain pieces of the missing metadata policy:
--   * legacy FRACTRAN prime transport preserves the 3/6/9 address;
--   * successful legacy prime transport records fromPositive residual approach;
--   * Hyperfabric owns the program/execution/normal/residual length carrier.
--
-- What the repo does not currently own is an exact map from the general
-- WeaveInstruction language to those legacy rules, nor per-instruction dynamics
-- for the description-length fields.  This module cross-pollinates the paid
-- pieces without silently identifying the two machines.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Biology.FRACTRANSSPTransitionExact as Legacy
import DASHI.Biology.SelfIndexingHyperfabricTetrationExact as Hyper
import DASHI.Biology.SignedSSPWeaveRichMetadataCompilerExact as Compiler
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

existingComplexityCarrier : Set
existingComplexityCarrier = Hyper.WeaveComplexity

fullMetadataDynamicsSocket : Set₁
fullMetadataDynamicsSocket = Compiler.RichMetadataDynamics

-- No constructor is supplied: a general WeaveInstruction-to-legacy-rule
-- compiler is not present in the source tree, and refineAt369 has no existing
-- address-transition semantics beyond its aggregate effect counter.

record SignedSSPWeaveMetadataAcquisitionBoundary : Set where
  constructor signed-ssp-weave-metadata-acquisition-boundary
  field
    legacyAddressPreservationPolicyLocated : Bool
    legacyResidualDirectionPolicyLocated : Bool
    typedComplexityCarrierLocated : Bool
    generalWeaveInstructionToLegacyRuleMapLocated : Bool
    refineAt369AddressDynamicsLocated : Bool
    perInstructionDescriptionLengthDynamicsLocated : Bool
    fullRichMetadataDynamicsRecovered : Bool

canonicalSignedSSPWeaveMetadataAcquisitionBoundary :
  SignedSSPWeaveMetadataAcquisitionBoundary
canonicalSignedSSPWeaveMetadataAcquisitionBoundary =
  signed-ssp-weave-metadata-acquisition-boundary
    true true true
    false false false false
