module DASHI.Interop.DistributedProofProducerABIExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- AGDA : SLR : LEAN/WIKI-PROVER DISTRIBUTED PRODUCER ABI
--
-- Architecture composition: Johl Brown discussion-origin proposal.
-- Concrete JMD/Lean/Wikidata and SLR implementations remain owned by their
-- source repositories.  This generic ABI and the non-promotion theorems are
-- DASHI synthesis; it does not reassign source ownership.
------------------------------------------------------------------------

data InquiryAction : Set where
  thinkAction : InquiryAction
  lookAction : InquiryAction
  reviewAction : InquiryAction

data ProducerClass : Set where
  slrAcquisitionProducer : ProducerClass
  leanWikiProverProducer : ProducerClass
  humanReviewProducer : ProducerClass
  agdaAdmissionInterpreter : ProducerClass
  namedProducer : String → ProducerClass

data ProofResultKind : Set where
  proofSucceeded : ProofResultKind
  proofFailed : ProofResultKind
  proofInconclusive : ProofResultKind

data ResidualDisposition : Set where
  discharged : ResidualDisposition
  refined : ResidualDisposition
  reopenLook : ResidualDisposition
  reopenThink : ResidualDisposition
  requireReview : ResidualDisposition

ownerOfAction : InquiryAction → ProducerClass
ownerOfAction thinkAction = leanWikiProverProducer
ownerOfAction lookAction = slrAcquisitionProducer
ownerOfAction reviewAction = humanReviewProducer

record ProofObligation : Set where
  constructor proofObligation
  field
    obligationId : String
    worldRevision : String
    sourceBindings : String
    authorityContext : String
    query : String

open ProofObligation public

record ProofReceipt : Set where
  constructor proofReceipt
  field
    obligation : ProofObligation
    producer : ProducerClass
    checkerIdentity : String
    checkerVersion : String
    artifactIdentity : String
    resultKind : ProofResultKind
    dependencySummary : String
    residualSummary : String
    executionObserved : Bool
    createsPromotion : Bool
    createsPromotionIsFalse : createsPromotion ≡ false
    createsPremiseAuthority : Bool
    createsPremiseAuthorityIsFalse : createsPremiseAuthority ≡ false

open ProofReceipt public

record ProducerRunResult : Set where
  constructor producerRunResult
  field
    receipt : ProofReceipt
    disposition : ResidualDisposition
    mayReenterSLR : Bool

open ProducerRunResult public

record ProofProducerABI : Set where
  constructor proofProducerABI
  field
    producerClass : ProducerClass
    supportedAction : InquiryAction
    checkerName : String
    sourceAcquisitionAuthority : Bool
    humanReviewAuthority : Bool
    semanticPromotionAuthority : Bool

open ProofProducerABI public

leanWikiProverABI : ProofProducerABI
leanWikiProverABI =
  proofProducerABI
    leanWikiProverProducer
    thinkAction
    "Lean/wiki-prover bounded proof/search/check producer"
    false false false

slrLookABI : ProofProducerABI
slrLookABI =
  proofProducerABI
    slrAcquisitionProducer
    lookAction
    "SLR acquisition / source / residual recurrence producer"
    true false false

humanReviewABI : ProofProducerABI
humanReviewABI =
  proofProducerABI
    humanReviewProducer
    reviewAction
    "human/institutional review producer"
    false true false

agdaAdmissionABI : ProofProducerABI
agdaAdmissionABI =
  proofProducerABI
    agdaAdmissionInterpreter
    reviewAction
    "Agda/DASHI semantic contract interpreter; an admission witness remains separately required"
    false false false

------------------------------------------------------------------------
-- Exact revision binding: a receipt says only what checker ran over exactly
-- which obligation/world/source coordinates.  It cannot silently float to a
-- later world revision.
------------------------------------------------------------------------

sameWorldRevision : ProofObligation → ProofObligation → Set
sameWorldRevision a b = worldRevision a ≡ worldRevision b

------------------------------------------------------------------------
-- Firewalls.  Think cannot pay Look or Review debt merely by theorem search.
------------------------------------------------------------------------

data ProofReceiptCreatesPromotion : Set where
data CheckerSuccessCreatesPremiseAuthority : Set where
data ThinkPaysMissingSource : Set where
data ThinkPaysHumanReview : Set where
data PaymentCreatesTruth : Set where
data ProofOverRevisionCreatesProofOverDifferentRevision : Set where

proofReceiptIsNotPromotion : ProofReceiptCreatesPromotion → ⊥
proofReceiptIsNotPromotion ()

checkerSuccessIsNotPremiseAuthority : CheckerSuccessCreatesPremiseAuthority → ⊥
checkerSuccessIsNotPremiseAuthority ()

thinkCannotPayMissingSource : ThinkPaysMissingSource → ⊥
thinkCannotPayMissingSource ()

thinkCannotPayHumanReview : ThinkPaysHumanReview → ⊥
thinkCannotPayHumanReview ()

paymentIsNotTruth : PaymentCreatesTruth → ⊥
paymentIsNotTruth ()

proofDoesNotFloatAcrossWorldRevision : ProofOverRevisionCreatesProofOverDifferentRevision → ⊥
proofDoesNotFloatAcrossWorldRevision ()

------------------------------------------------------------------------
-- Canonical recurrence fixture: an inconclusive Think result may reopen Look.
-- This demonstrates routing only; it is not an external-world observation.
------------------------------------------------------------------------

exampleObligation : ProofObligation
exampleObligation =
  proofObligation
    "example:missing-source-premise"
    "world-revision:example-1"
    "source-bindings:incomplete"
    "candidate-only"
    "Can the declared conclusion be discharged from admitted premises?"

exampleInconclusiveReceipt : ProofReceipt
exampleInconclusiveReceipt =
  proofReceipt
    exampleObligation
    leanWikiProverProducer
    "example-checker"
    "example-version"
    "receipt:example"
    proofInconclusive
    "admitted premises only"
    "missing source premise"
    true
    false refl
    false refl

exampleReentry : ProducerRunResult
exampleReentry =
  producerRunResult exampleInconclusiveReceipt reopenLook true
