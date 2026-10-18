module DASHI.Cognition.PNF.SensibLawConversationalSourceFamilyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawUnifiedPNFIntakeReentrySpineExact as M12

------------------------------------------------------------------------
-- S28.CHAT conversational source-family adapter.
--
-- Producer acquisition/archive ownership stays outside SLR.  SLR consumes
-- exact-coordinate archived messages and adapts selected exact message
-- subspans into the ordinary M12 SourceStatementEnvelope.
------------------------------------------------------------------------

data ConversationBranchMembership : Set where
  activeBranch inactiveBranch : ConversationBranchMembership

data ConversationRole : Set where
  userRole assistantRole toolRole systemRole otherRole : ConversationRole

data ConversationContentKind : Set where
  messageContent toolOutput fileContext artifactOutput :
    ConversationContentKind

record ArchivedConversationMessage : Set where
  constructor archived-conversation-message
  field
    conversationRef : String
    messageRef : String
    nodeRef : String
    parentNodeRef : String
    branchMembership : ConversationBranchMembership
    messageTimeRef : String
    role : ConversationRole
    threadTitle : String
    contentDigestRef : String
    contentKind : ConversationContentKind
    producerIdentityVerified : Bool
    producerIdentityVerifiedIsTrue : producerIdentityVerified ≡ true
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open ArchivedConversationMessage public

record MessageStatementWeld
    (message : ArchivedConversationMessage) : Set where
  constructor message-statement-weld
  field
    statement : M12.SourceStatementEnvelope
    exactMessageSubspanRef : String
    splitterReceiptRef : String
    messageIdentityEqualsStatementIdentity : Bool
    messageIdentityEqualsStatementIdentityIsFalse :
      messageIdentityEqualsStatementIdentity ≡ false
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open MessageStatementWeld public

------------------------------------------------------------------------
-- Source-role / branch boundary.
------------------------------------------------------------------------

record ConversationalSourceBoundary : Set where
  constructor conversational-source-boundary
  field
    originalConversationIdentityRequired : Bool
    originalMessageIdentityRequired : Bool
    nodeParentIdentityRequired : Bool
    branchMembershipRequired : Bool
    payloadIdentityVerificationRequired : Bool
    inactiveAssistantBranchIsWorldEvidence : Bool
    assistantProseIsSourceArtifact : Bool
    toolOutputIsReviewedObservation : Bool
    fileContextCreatesSemanticAuthority : Bool
    citationTokenIsVerifiedCitation : Bool
    messageTimeEqualsDescribedEventTime : Bool
    messageEqualsStatement : Bool

canonicalConversationalSourceBoundary : ConversationalSourceBoundary
canonicalConversationalSourceBoundary =
  conversational-source-boundary
    true true true true true
    false false false false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MessageIsStatement : Set where
data MessageIsWorldFact : Set where
data InactiveAssistantBranchIsIndependentWorldAccount : Set where
data AssistantProseIsSourceArtifact : Set where
data ToolOutputIsReviewedObservation : Set where
data FileContextIsSemanticAuthority : Set where
data CitationTokenIsVerifiedCitation : Set where
data MessageTimeIsEventTime : Set where
data CanonicalArchiveHashMayReplaceOriginalMessageIdentity : Set where
data BranchMembershipMayBeDiscarded : Set where

messageIsNotStatement : MessageIsStatement → ⊥
messageIsNotStatement ()

messageIsNotWorldFact : MessageIsWorldFact → ⊥
messageIsNotWorldFact ()

inactiveAssistantBranchIsNotAutomaticallyWorldAccount :
  InactiveAssistantBranchIsIndependentWorldAccount → ⊥
inactiveAssistantBranchIsNotAutomaticallyWorldAccount ()

assistantProseIsNotSourceArtifact :
  AssistantProseIsSourceArtifact → ⊥
assistantProseIsNotSourceArtifact ()

toolOutputIsNotReviewedObservation :
  ToolOutputIsReviewedObservation → ⊥
toolOutputIsNotReviewedObservation ()

fileContextDoesNotCreateSemanticAuthority :
  FileContextIsSemanticAuthority → ⊥
fileContextDoesNotCreateSemanticAuthority ()

citationTokenDoesNotVerifyCitation :
  CitationTokenIsVerifiedCitation → ⊥
citationTokenDoesNotVerifyCitation ()

messageTimeDoesNotBecomeEventTime :
  MessageTimeIsEventTime → ⊥
messageTimeDoesNotBecomeEventTime ()

canonicalArchiveHashCannotReplaceOriginalMessageIdentity :
  CanonicalArchiveHashMayReplaceOriginalMessageIdentity → ⊥
canonicalArchiveHashCannotReplaceOriginalMessageIdentity ()

branchMembershipMayNotBeDiscarded :
  BranchMembershipMayBeDiscarded → ⊥
branchMembershipMayNotBeDiscarded ()
