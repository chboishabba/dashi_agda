module DASHI.Unified.TOEGovernanceSemanticNonPromotionValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Interop.SensibLawSemanticPromotionPolicy as SensibLaw
import DASHI.Unified.GovernedLegalWorkflowTOEBridgeRegression
import DASHI.Unified.TOEGovernanceSemanticNonPromotionExact as Governance

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
  Governance.toeRuntimeCoordinateCompletenessDoesNotProveFormalAdequacy
  ≡ Governance.toeRuntimeCoordinateCompletenessDoesNotProveFormalAdequacy
_ = refl

_ :
  Governance.toeTheoremBackedAdequacyRequiresAdequateFor
  ≡ Governance.toeTheoremBackedAdequacyRequiresAdequateFor
_ = refl

_ :
  Governance.toeApproximateCollisionCannotPromoteExactResidual
  ≡ Governance.toeApproximateCollisionCannotPromoteExactResidual
_ = refl

_ :
  Governance.toeFrontierClosureDoesNotProveConsumerAdequacy
  ≡ Governance.toeFrontierClosureDoesNotProveConsumerAdequacy
_ = refl

_ :
  Governance.toeNoFreshDemandDoesNotProveConsumerAdequacy
  ≡ Governance.toeNoFreshDemandDoesNotProveConsumerAdequacy
_ = refl

_ :
  Governance.toeExactNonfactorabilityMayReopenClosedFrontier
  ≡ Governance.toeExactNonfactorabilityMayReopenClosedFrontier
_ = refl

_ :
  Governance.toeRevisionChangeReopensContextBeforeIdentity
  ≡ Governance.toeRevisionChangeReopensContextBeforeIdentity
_ = refl

_ :
  Governance.toeLatestRevisionLookupDoesNotPayContextReview
  ≡ Governance.toeLatestRevisionLookupDoesNotPayContextReview
_ = refl

_ :
  Governance.toeRevisionReopenDoesNotCreateClaimTruth
  ≡ Governance.toeRevisionReopenDoesNotCreateClaimTruth
_ = refl

_ :
  Governance.toeRevisionRereviewDoesNotChangeClaimTruth
  ≡ Governance.toeRevisionRereviewDoesNotChangeClaimTruth
_ = refl

_ :
  Governance.toeRevisionDoesNotAutomaticallyRefutePriorEvidence
  ≡ Governance.toeRevisionDoesNotAutomaticallyRefutePriorEvidence
_ = refl
