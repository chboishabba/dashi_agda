module DASHI.Unified.TOEGovernanceSemanticNonPromotionValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Interop.SensibLawSemanticPromotionPolicy as SensibLaw
import DASHI.Unified.GovernedLegalWorkflowTOEBridgeRegression
import DASHI.Unified.TOEGovernanceSemanticNonPromotionExact as Governance
import DASHI.Law.ConsumerAdequacyRuntimeTheoremBridgeExact as Adequacy
import DASHI.Law.ExactNonFactorabilityResidualCompilerExact as NonFactor
import DASHI.Law.ConsumerResearchAdmissibilityStopExact as ResearchStop
import DASHI.Law.ClosedIsNotAdequateExact as Closed
import DASHI.Law.MaboRevisionReopenExact as MaboRevision
import DASHI.Law.RevisionReReviewPropagationExact as RevisionReview
import DASHI.Law.LegalWorldRevisionReconstructionExact as WorldRevision

_ :
  Authority.legalAuthorityFlag
    (Governance.authorityBoundary Governance.canonicalTOEGovernanceHandoff)
  ≡ false
_ = SensibLaw.semantic-promotion-legal-authority-closed

_ :
  Authority.promotesAnyAuthority
    (Governance.authorityBoundary Governance.canonicalTOEGovernanceHandoff)
  ≡ false
_ = SensibLaw.semantic-promotion-all-authority-closed

_ :
  Authority.legalAuthorityFlag Governance.actionstepWorkflowBoundary
  ≡ false
_ = Governance.actionstepLegalAuthorityClosed

_ :
  Authority.promotesAnyAuthority Governance.actionstepWorkflowBoundary
  ≡ false
_ = Governance.actionstepAnyAuthorityClosed


------------------------------------------------------------------------
-- Legal/research normalized non-promotion checks.
------------------------------------------------------------------------


_ :
  Adequacy.runtimeCoordinateCompletenessIsFormalAdequacy
    Adequacy.canonicalConsumerAdequacyRuntimeTheoremBridgeBoundary
  ≡ false
_ = Governance.toeRuntimeCoordinateCompletenessDoesNotProveFormalAdequacy

_ :
  Adequacy.theoremBackedReceiptRequiresAdequateForInhabitant
    Adequacy.canonicalConsumerAdequacyRuntimeTheoremBridgeBoundary
  ≡ true
_ = Governance.toeTheoremBackedAdequacyRequiresAdequateFor

_ :
  NonFactor.approximateCollisionMayPromoteExactResidual
    NonFactor.canonicalExactNonFactorabilityResidualCompilerBoundary
  ≡ false
_ = Governance.toeApproximateCollisionCannotPromoteExactResidual

_ :
  ResearchStop.frontierClosureAloneProvesConsumerAdequacy
    ResearchStop.canonicalConsumerResearchAdmissibilityStopBoundary
  ≡ false
_ = Governance.toeFrontierClosureDoesNotProveConsumerAdequacy

_ :
  Closed.noFreshDemandIsConsumerAdequacyProof
    Closed.canonicalClosedIsNotAdequateBoundary
  ≡ false
_ = Governance.toeNoFreshDemandDoesNotProveConsumerAdequacy

_ :
  Closed.exactNonfactorabilityMayReopenClosedFrontier
    Closed.canonicalClosedIsNotAdequateBoundary
  ≡ true
_ = Governance.toeExactNonfactorabilityMayReopenClosedFrontier

_ :
  MaboRevision.revisionChangeReopensContextBeforeIdentity
    MaboRevision.canonicalMaboRevisionReopenBoundary
  ≡ true
_ = Governance.toeRevisionChangeReopensContextBeforeIdentity

_ :
  MaboRevision.latestRevisionLookupPaysContextReview
    MaboRevision.canonicalMaboRevisionReopenBoundary
  ≡ false
_ = Governance.toeLatestRevisionLookupDoesNotPayContextReview

_ :
  MaboRevision.revisionReopenCreatesClaimTruth
    MaboRevision.canonicalMaboRevisionReopenBoundary
  ≡ false
_ = Governance.toeRevisionReopenDoesNotCreateClaimTruth

_ :
  RevisionReview.rereviewAutomaticallyChangesClaimTruth
    RevisionReview.canonicalRevisionReReviewPropagationBoundary
  ≡ false
_ = Governance.toeRevisionRereviewDoesNotChangeClaimTruth

_ :
  WorldRevision.revisionAutomaticallyRefutesPriorEvidence
    WorldRevision.canonicalLegalWorldRevisionReconstructionBoundary
  ≡ false
_ = Governance.toeRevisionDoesNotAutomaticallyRefutePriorEvidence
