module DASHI.Interop.SLRConsumerResidualCompilerParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRSpacyObservationWorldCompilerParityExact as Compiler
import DASHI.Interop.SLRBinaryWorldWireParityExact as WorldWire
import DASHI.Reasoning.SemanticConsumerRelativeClosureExact as ConsumerClosure
import DASHI.Interop.SLRFragmentEvidenceContractionExact as EvidenceContraction

------------------------------------------------------------------------
-- BINARY CONSUMER-RESIDUAL COMPILER PARITY
--
-- Runtime owner:
--   chboishabba/slr :: crates/sl-consumer-residual
--
-- Consumer wire v1:
--   magic[4] = "SLRC"
--   version  = u16 little-endian 1
--   consumerId : length-prefixed UTF-8
--   surfaceId  : length-prefixed UTF-8
--   requirementCount : u32 little-endian
--   repeated requirement:
--     requirementId : length-prefixed UTF-8
--     fragmentTag   : u8, exact CompilerFragmentKind tag
--     scopeTag      : u8, 0 = any source, 1 = exact source manifestation
--     sourceRef     : length-prefixed UTF-8 only when scopeTag = 1
--
-- A candidate PNF pays only the declared observation requirement when its
-- fragment family matches and the optional source-manifestation scope matches.
-- Payment does not promote claim truth, semantic equivalence or authority.
------------------------------------------------------------------------

consumerWireVersion : Nat
consumerWireVersion = 1

data ConsumerScope : Set where
  anySource : ConsumerScope
  sourceManifestation : String → ConsumerScope

record ConsumerRequirement : Set where
  constructor consumerRequirement
  field
    requirementReference : String
    fragmentKind : Compiler.CompilerFragmentKind
    scope : ConsumerScope

open ConsumerRequirement public

record BinaryConsumerSpec : Set where
  constructor binaryConsumerSpec
  field
    consumerReference : String
    surfaceReference : String
    requirements : List ConsumerRequirement

open BinaryConsumerSpec public

record CandidateObservationCoordinate : Set where
  constructor candidateObservationCoordinate
  field
    candidateReference : String
    sourceManifestationReference : String
    fragmentKindObserved : Compiler.CompilerFragmentKind
    candidateOnly : Bool
    semanticPromotion : Bool

open CandidateObservationCoordinate public

record RequirementPaymentReceipt
    (requirement : ConsumerRequirement)
    (candidate : CandidateObservationCoordinate) : Set where
  constructor requirementPaymentReceipt
  field
    fragmentFamilyMatches : Bool
    sourceScopeMatches : Bool
    candidateOnlyRetained : Bool
    semanticPromotionRetainedFalse : Bool
    requirementPaid : Bool
    paymentCreatesClaimTruth : Bool
    paymentCreatesSemanticEquivalence : Bool
    paymentCreatesSourceAuthority : Bool

open RequirementPaymentReceipt public

------------------------------------------------------------------------
-- Output body contracts.  Both are kind-owned binary payloads inside the
-- already formalised SLRW envelope.
--
-- GAP1 body:
--   "GAP1" | fragment:u8 | candidateOnly:u8=1 | semanticPromotion:u8=0 |
--   consumerId:text | requirementId:text | scopeTag:u8 | [sourceRef:text]
--
-- OBL1 body has the identical coordinate payload under magic "OBL1".
------------------------------------------------------------------------

record ConsumerResidualBodyParity : Set where
  constructor consumerResidualBodyParity
  field
    gapMagicIsGAP1 : Bool
    obligationMagicIsOBL1 : Bool
    fragmentTagUsesCompilerMapping : Bool
    candidateOnlyByteIsOne : Bool
    semanticPromotionByteIsZero : Bool
    consumerReferenceRetained : Bool
    requirementReferenceRetained : Bool
    scopeCoordinateRetained : Bool
    exactSourceReferenceRetainedWhenScoped : Bool

open ConsumerResidualBodyParity public

canonicalConsumerResidualBodyParity : ConsumerResidualBodyParity
canonicalConsumerResidualBodyParity =
  consumerResidualBodyParity
    true true true true true true true true true

record ConsumerResidualRuntimeParity : Set where
  constructor consumerResidualRuntimeParity
  field
    magicIsSLRC : Bool
    versionIsOne : Bool
    binaryOnlyConsumerSpec : Bool
    fragmentTagMappingExact : Bool
    sourceScopeIsOptionalAndExplicit : Bool
    incomingSLRWFramesPreserved : Bool
    paidRequirementEmitsGap : Bool
    paidRequirementEmitsObligation : Bool
    unpaidRequirementEmitsExactlyOneGap : Bool
    unpaidRequirementEmitsExactlyOneObligation : Bool
    gapUsesConsumerSurfaceAsAuxCoordinate : Bool
    obligationUsesNeedFragmentKindAsAuxCoordinate : Bool
    otherSourceMayPayExactSourceRequirement : Bool
    paymentCreatesClaimTruth : Bool
    paymentCreatesSemanticEquivalence : Bool
    paymentCreatesSourceAuthority : Bool
    postgresPerformsRequirementMatching : Bool
    jsonConsumerTransportUsed : Bool
    regexRequirementParserUsed : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open ConsumerResidualRuntimeParity public

canonicalConsumerResidualRuntimeParity : ConsumerResidualRuntimeParity
canonicalConsumerResidualRuntimeParity =
  consumerResidualRuntimeParity
    true true true true true true
    false false true true true true
    false false false false false false false
    true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OtherSourcePaysExactScopedRequirement : Set where
data ConsumerPaymentCreatesClaimTruth : Set where
data ConsumerPaymentCreatesSemanticEquivalence : Set where
data ConsumerPaymentCreatesSourceAuthority : Set where
data PostgresMatchesConsumerRequirements : Set where
data JsonConsumerTransport : Set where
data RegexConsumerRequirementParser : Set where

otherSourceCannotPayExactScopedRequirement : OtherSourcePaysExactScopedRequirement → ⊥
otherSourceCannotPayExactScopedRequirement ()

consumerPaymentDoesNotCreateClaimTruth : ConsumerPaymentCreatesClaimTruth → ⊥
consumerPaymentDoesNotCreateClaimTruth ()

consumerPaymentDoesNotCreateSemanticEquivalence : ConsumerPaymentCreatesSemanticEquivalence → ⊥
consumerPaymentDoesNotCreateSemanticEquivalence ()

consumerPaymentDoesNotCreateSourceAuthority : ConsumerPaymentCreatesSourceAuthority → ⊥
consumerPaymentDoesNotCreateSourceAuthority ()

postgresDoesNotMatchConsumerRequirements : PostgresMatchesConsumerRequirements → ⊥
postgresDoesNotMatchConsumerRequirements ()

jsonConsumerTransportForbidden : JsonConsumerTransport → ⊥
jsonConsumerTransportForbidden ()

regexConsumerRequirementParserForbidden : RegexConsumerRequirementParser → ⊥
regexConsumerRequirementParserForbidden ()

------------------------------------------------------------------------
-- Existing-owner anchors: consumer-relative closure and append-only evidence
-- contraction remain the semantic parents; this module only fixes the runtime
-- binary ABI and the first executable observation-payment rule.
------------------------------------------------------------------------

consumerClosureBoundaryAnchor : ConsumerClosure.SemanticConsumerClosureBoundary
consumerClosureBoundaryAnchor = ConsumerClosure.canonicalSemanticConsumerClosureBoundary

evidenceContractionBoundaryAnchor : EvidenceContraction.FragmentEvidenceContractionBoundary
evidenceContractionBoundaryAnchor = EvidenceContraction.canonicalFragmentEvidenceContractionBoundary

consumerResidualTargetsWorldWireVersion : Nat
consumerResidualTargetsWorldWireVersion = WorldWire.wireVersion
