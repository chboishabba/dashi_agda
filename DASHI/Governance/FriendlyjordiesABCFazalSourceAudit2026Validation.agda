module DASHI.Governance.FriendlyjordiesABCFazalSourceAudit2026Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Governance.FriendlyjordiesABCFazalSourceAudit2026Exact as A

sourceWarningsRemainContested :
  A.disposition A.warningReported ≡ A.reportedWithDenial
sourceWarningsRemainContested = refl

suspectScreenGrabUnauthenticated :
  A.disposition A.messagesDisputed ≡ A.reportedWithDenial
suspectScreenGrabUnauthenticated = refl

ombudsmanFindingHasEditorialScope :
  A.kind A.abcOmbudsmansDetermination ≡ A.independentEditorialFinding
ombudsmanFindingHasEditorialScope = refl

institutionAcceptedEditorialCorrection :
  A.kind A.abcProgramsRemoved ≡ A.publishedCorrection
institutionAcceptedEditorialCorrection = refl

ombudsmanFindingDoesNotPayThreat :
  A.ombudsmanEditorialBreachProvesThreat A.canonicalSafetyAndReportingBoundary ≡ false
ombudsmanFindingDoesNotPayThreat = refl

disputedScreenshotsNotVerifiedByHeadline :
  A.disputed2025ScreenshotsAreAuthenticated A.canonicalSafetyAndReportingBoundary ≡ false
disputedScreenshotsNotVerifiedByHeadline = refl

investigationCanBeAuditedSeparately :
  A.institutionalReviewCanTestInternalEscalation A.canonicalSafetyAndReportingBoundary ≡ true
investigationCanBeAuditedSeparately = refl

arsonMastermindNotProven :
  A.arsonPerpetratorConvictionIdentifiesMastermind A.canonicalSafetyAndReportingBoundary ≡ false
arsonMastermindNotProven = refl

editorialFailureNotCriminalThreat : A.EditorialBreachProvesThreat → ⊥
editorialFailureNotCriminalThreat = A.noThreatPromotion

arsonProsecutionNoCommand : A.ArsonConvictionProvesMastermind → ⊥
arsonProsecutionNoCommand = A.noMastermindPromotion

screenshotProvenanceRequired : A.DisputedMessagesBecomeAuthenticByPublication → ⊥
screenshotProvenanceRequired = A.noScreenGrabTruthPromotion

institutionalReplyIsNotCoverupProof : A.ABCResponseProvesConspiracy → ⊥
institutionalReplyIsNotCoverupProof = A.noCoverupPromotion

-- Only original Ombudsman summary supports the actual source-specific
-- standards. The 2024 warnings are outside this review's criminal scope.
findingOneIsAccuracy :
  A.editorialStandard A.finding1DoublePresentation ≡ "accuracy 2.2"
findingOneIsAccuracy = refl

findingThreeIsUpwardReferral :
  A.editorialStandard A.finding3SweeperApproval ≡ "fair and honest dealing 5.9c"
findingThreeIsUpwardReferral = refl

findingFiveIsInstitutionalIntegrity :
  A.editorialStandard A.finding5InstitutionalIntegrity ≡ "independence and integrity 1.1"
findingFiveIsInstitutionalIntegrity = refl

r4AcceptedByABC :
  A.abcPubliclyAccepted A.r4NamedAnonymityApprover ≡ true
r4AcceptedByABC = refl

r4NotIndependentlyAudited :
  A.independentlyVerifiedImplementation A.r4NamedAnonymityApprover ≡ false
r4NotIndependentlyAudited = refl

acceptanceDoesNotVerifyCompletion :
  A.InstitutionalAcceptanceImpliesAuditedCompletion → ⊥
acceptanceDoesNotVerifyCompletion =
  A.institutionalAcceptanceDoesNotPayCompletion
