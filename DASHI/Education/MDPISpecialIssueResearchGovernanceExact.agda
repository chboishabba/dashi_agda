module DASHI.Education.MDPISpecialIssueResearchGovernanceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- SOURCE-EXACT PUBLICATION GOVERNANCE
--
-- MDPI's Special Issue guidance separates promotion/invitation, peer review,
-- editorial decision, publication administration, authorship/accountability,
-- and research evidence.  The ethics page separately governs substantive
-- GenAI use, human accountability, reviewer/editor AI use, conflicts of
-- interest, human-participant ethics and data availability.
--
-- None of these publication-process roles manufacture empirical evidence.
------------------------------------------------------------------------

data GovernanceRole : Set where
  guestEditorRole : GovernanceRole
  editorialBoardRole : GovernanceRole
  editorialOfficeRole : GovernanceRole
  reviewerRole : GovernanceRole
  authorRole : GovernanceRole
  participantRole : GovernanceRole
  genAIToolRole : GovernanceRole

data GovernanceOperation : Set where
  promotionOperation : GovernanceOperation
  invitationOperation : GovernanceOperation
  peerReviewOperation : GovernanceOperation
  editorialDecisionOperation : GovernanceOperation
  authorshipOperation : GovernanceOperation
  contributionOperation : GovernanceOperation
  accountabilityOperation : GovernanceOperation
  consentOperation : GovernanceOperation
  evidenceOperation : GovernanceOperation
  independentHandlingOperation : GovernanceOperation
  genAIDisclosureOperation : GovernanceOperation

record AcquisitionReceipt : Set where
  constructor acquisitionReceipt
  field
    sourceURL : String
    localSnapshot : String
    acquiredOn : String

open AcquisitionReceipt public

data InvitationPromotesEvidence : Set where

invitationDoesNotPromoteEvidence : InvitationPromotesEvidence → ⊥
invitationDoesNotPromoteEvidence ()

data GenAIPromotesAuthor : Set where

genAIDoesNotPromoteAuthor : GenAIPromotesAuthor → ⊥
genAIDoesNotPromoteAuthor ()

data ConflictedGuestEditorMayHandleManuscript : Set where

conflictedGuestEditorCannotHandleManuscript :
  ConflictedGuestEditorMayHandleManuscript → ⊥
conflictedGuestEditorCannotHandleManuscript ()

data GenAIProducesSubstantiveReview : Set where

genAICannotProduceSubstantiveReview : GenAIProducesSubstantiveReview → ⊥
genAICannotProduceSubstantiveReview ()

data GenAIMakesEditorialDecision : Set where

genAICannotMakeEditorialDecision : GenAIMakesEditorialDecision → ⊥
genAICannotMakeEditorialDecision ()

record MDPISpecialIssueResearchGovernance : Set where
  constructor mdpiSpecialIssueResearchGovernance
  field
    governanceRoles : List GovernanceRole
    governanceOperations : List GovernanceOperation

    ethicsSnapshots : List AcquisitionReceipt
    snapshotsAreAcquisitionsNotIndependentAuthorities : Bool
    snapshotsAreAcquisitionsNotIndependentAuthoritiesIsTrue :
      snapshotsAreAcquisitionsNotIndependentAuthorities ≡ true

    invitationIsPromotionNotEvidence : Bool
    invitationIsPromotionNotEvidenceIsTrue : invitationIsPromotionNotEvidence ≡ true

    guestEditorConflictRequiresIndependentHandling : Bool
    guestEditorConflictRequiresIndependentHandlingIsTrue :
      guestEditorConflictRequiresIndependentHandling ≡ true

    substantiveGenAIUseRequiresDisclosure : Bool
    substantiveGenAIUseRequiresDisclosureIsTrue :
      substantiveGenAIUseRequiresDisclosure ≡ true

    genAIQualifiesAsAuthor : Bool
    genAIQualifiesAsAuthorIsFalse : genAIQualifiesAsAuthor ≡ false

    humanAuthorsRetainAccountability : Bool
    humanAuthorsRetainAccountabilityIsTrue :
      humanAuthorsRetainAccountability ≡ true

    reviewerGenAIProducesSubstantiveReview : Bool
    reviewerGenAIProducesSubstantiveReviewIsFalse :
      reviewerGenAIProducesSubstantiveReview ≡ false

    academicEditorGenAIDecisionMaking : Bool
    academicEditorGenAIDecisionMakingIsFalse :
      academicEditorGenAIDecisionMaking ≡ false

    editorialOfficeComplianceChecksCreateResearchEvidence : Bool
    editorialOfficeComplianceChecksCreateResearchEvidenceIsFalse :
      editorialOfficeComplianceChecksCreateResearchEvidence ≡ false

    apcOrPaymentMayControlEditorialDecision : Bool
    apcOrPaymentMayControlEditorialDecisionIsFalse :
      apcOrPaymentMayControlEditorialDecision ≡ false

open MDPISpecialIssueResearchGovernance public

canonicalMDPISpecialIssueResearchGovernance : MDPISpecialIssueResearchGovernance
canonicalMDPISpecialIssueResearchGovernance =
  mdpiSpecialIssueResearchGovernance
    ( guestEditorRole
    ∷ editorialBoardRole
    ∷ editorialOfficeRole
    ∷ reviewerRole
    ∷ authorRole
    ∷ participantRole
    ∷ genAIToolRole
    ∷ []
    )
    ( promotionOperation
    ∷ invitationOperation
    ∷ peerReviewOperation
    ∷ editorialDecisionOperation
    ∷ authorshipOperation
    ∷ contributionOperation
    ∷ accountabilityOperation
    ∷ consentOperation
    ∷ evidenceOperation
    ∷ independentHandlingOperation
    ∷ genAIDisclosureOperation
    ∷ []
    )
    ( acquisitionReceipt
        "https://www.mdpi.com/ethics"
        "Pasted markdown (2)(20260915-225217).md"
        "2026-09-15"
    ∷ acquisitionReceipt
        "https://www.mdpi.com/ethics"
        "Pasted markdown (3)(20260915-225227).md"
        "2026-09-15"
    ∷ []
    )
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Current source-specific projections used by downstream bridges.
------------------------------------------------------------------------

guestEditorConflictIndependentHandlingIsRequired :
  guestEditorConflictRequiresIndependentHandling
    canonicalMDPISpecialIssueResearchGovernance ≡ true
guestEditorConflictIndependentHandlingIsRequired = refl

substantiveGenAIDisclosureIsRequired :
  substantiveGenAIUseRequiresDisclosure
    canonicalMDPISpecialIssueResearchGovernance ≡ true
substantiveGenAIDisclosureIsRequired = refl

humanAuthorsRemainAccountable :
  humanAuthorsRetainAccountability
    canonicalMDPISpecialIssueResearchGovernance ≡ true
humanAuthorsRemainAccountable = refl

reviewerGenAICannotGenerateSubstantiveReview :
  reviewerGenAIProducesSubstantiveReview
    canonicalMDPISpecialIssueResearchGovernance ≡ false
reviewerGenAICannotGenerateSubstantiveReview = refl

academicEditorGenAICannotMakeDecision :
  academicEditorGenAIDecisionMaking
    canonicalMDPISpecialIssueResearchGovernance ≡ false
academicEditorGenAICannotMakeDecision = refl
