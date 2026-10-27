module DASHI.Unified.TOEGovernanceSemanticNonPromotionValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Interop.SensibLawSemanticPromotionPolicy as SensibLaw
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
