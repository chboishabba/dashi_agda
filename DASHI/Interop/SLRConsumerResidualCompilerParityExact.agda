module DASHI.Interop.SLRConsumerResidualCompilerParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRBinaryWorldWireParityExact as WorldWire
import DASHI.Interop.SLRConsumerRequirementV2Exact as ConsumerV2
import DASHI.Reasoning.SemanticConsumerRelativeClosureExact as ConsumerClosure
import DASHI.Interop.SLRFragmentEvidenceContractionExact as EvidenceContraction

------------------------------------------------------------------------
-- Canonical consumer-residual runtime boundary.
-- Requirement syntax and coordinate tags are owned by SLRC v2.
------------------------------------------------------------------------

consumerWireVersion : Nat
consumerWireVersion = ConsumerV2.consumerWireVersion

legacyConsumerWireVersion : Nat
legacyConsumerWireVersion = ConsumerV2.legacyConsumerWireVersion

gapWorldWireKindTag : Nat
gapWorldWireKindTag = WorldWire.worldWireKindTag WorldWire.gap

obligationWorldWireKindTag : Nat
obligationWorldWireKindTag = WorldWire.worldWireKindTag WorldWire.obligation

paymentWorldWireKindTag : Nat
paymentWorldWireKindTag = WorldWire.worldWireKindTag WorldWire.payment

record ConsumerResidualRuntimeParity : Set where
  constructor consumerResidualRuntimeParity
  field
    magicIsSLRC : Bool
    productionVersionIsTwo : Bool
    legacyV1ReplayDecodeRetained : Bool
    binaryOnlyConsumerSpec : Bool
    typedRequirementClassesExact : Bool
    incomingSLRWFramesPreserved : Bool
    pnfFragmentMayPayMatchingFragmentRequirement : Bool
    pnfFragmentMayPayEvidenceCoordinate : Bool
    paidFragmentRequirementEmitsTwoPAY1Receipts : Bool
    unpaidFragmentEmitsGAP1OBL1 : Bool
    unpaidEvidenceEmitsGAP2OBL2 : Bool
    exactSourceScopeRetained : Bool
    paymentUsesExactResidualId : Bool
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
    true true true true true true true false true true true true true
    false false false false false false true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PNFDirectlyPaysEvidenceCoordinate : Set where
data ConsumerPaymentCreatesClaimTruth : Set where
data ConsumerPaymentCreatesSemanticEquivalence : Set where
data ConsumerPaymentCreatesSourceAuthority : Set where
data PostgresMatchesConsumerRequirements : Set where
data JsonConsumerTransport : Set where
data RegexConsumerRequirementParser : Set where

pnfCannotDirectlyPayEvidenceCoordinate : PNFDirectlyPaysEvidenceCoordinate → ⊥
pnfCannotDirectlyPayEvidenceCoordinate ()

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

consumerRequirementV2Anchor : ConsumerV2.ConsumerRequirementV2Parity
consumerRequirementV2Anchor = ConsumerV2.canonicalConsumerRequirementV2Parity

consumerResidualTargetsWorldWireVersion : Nat
consumerResidualTargetsWorldWireVersion = WorldWire.wireVersion
