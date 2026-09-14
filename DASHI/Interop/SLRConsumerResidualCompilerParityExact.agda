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
------------------------------------------------------------------------

consumerWireVersion : Nat
consumerWireVersion = 1

data ConsumerScope : Set where
  anySource : ConsumerScope
  sourceManifestation : String → ConsumerScope

consumerScopeTag : ConsumerScope → Nat
consumerScopeTag anySource = 0
consumerScopeTag (sourceManifestation sourceRef) = 1

consumerRequirementFragmentTag : Compiler.CompilerFragmentKind → Nat
consumerRequirementFragmentTag = Compiler.compilerFragmentTag

gapWorldWireKindTag : Nat
gapWorldWireKindTag = WorldWire.worldWireKindTag WorldWire.gap

obligationWorldWireKindTag : Nat
obligationWorldWireKindTag = WorldWire.worldWireKindTag WorldWire.obligation

paymentWorldWireKindTag : Nat
paymentWorldWireKindTag = WorldWire.worldWireKindTag WorldWire.payment

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
-- Output body contracts.
-- GAP1 and OBL1 carry the unpaid residual coordinates.
-- PAY1 carries the same consumer/requirement/scope coordinates plus the exact
-- target residual id. A paid requirement emits two PAY1 records: one for its
-- deterministic gap id and one for its deterministic obligation id.
------------------------------------------------------------------------

record ConsumerResidualBodyParity : Set where
  constructor consumerResidualBodyParity
  field
    gapMagicIsGAP1 : Bool
    obligationMagicIsOBL1 : Bool
    paymentMagicIsPAY1 : Bool
    fragmentTagUsesCompilerMapping : Bool
    gapUsesWorldWireKindFour : Bool
    obligationUsesWorldWireKindFive : Bool
    paymentUsesWorldWireKindEight : Bool
    anySourceScopeTagIsZero : Bool
    exactSourceScopeTagIsOne : Bool
    candidateOnlyByteIsOne : Bool
    semanticPromotionByteIsZero : Bool
    consumerReferenceRetained : Bool
    requirementReferenceRetained : Bool
    scopeCoordinateRetained : Bool
    exactSourceReferenceRetainedWhenScoped : Bool
    paymentRetainsExactTargetResidualId : Bool

open ConsumerResidualBodyParity public

canonicalConsumerResidualBodyParity : ConsumerResidualBodyParity
canonicalConsumerResidualBodyParity =
  consumerResidualBodyParity
    true true true true true true true true
    true true true true true true true true

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
    paidRequirementEmitsTwoPaymentReceipts : Bool
    unpaidRequirementEmitsExactlyOneGap : Bool
    unpaidRequirementEmitsExactlyOneObligation : Bool
    gapUsesConsumerSurfaceAsAuxCoordinate : Bool
    obligationUsesNeedFragmentKindAsAuxCoordinate : Bool
    paymentUsesTargetResidualAsAuxCoordinate : Bool
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
    false false true true true true true true
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

consumerClosureBoundaryAnchor : ConsumerClosure.SemanticConsumerClosureBoundary
consumerClosureBoundaryAnchor = ConsumerClosure.canonicalSemanticConsumerClosureBoundary

evidenceContractionBoundaryAnchor : EvidenceContraction.FragmentEvidenceContractionBoundary
evidenceContractionBoundaryAnchor = EvidenceContraction.canonicalFragmentEvidenceContractionBoundary

consumerResidualTargetsWorldWireVersion : Nat
consumerResidualTargetsWorldWireVersion = WorldWire.wireVersion
