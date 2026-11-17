module DASHI.Unified.GovernedLegalWorkflowSourceSemanticTOERegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.GovernedLegalWorkflowSourceSemanticTOEExact as Handoff
import DASHI.Unified.GovernedLegalWorkflowSourceGenealogyTOEExact as LegalSource
import DASHI.Unified.PNFDistilledNonPromotionTOEExact as Distilled
import DASHI.Unifier as Unifier

legalSourceHandoffIsCanonical :
  Handoff.legalSourceGenealogyHandoff
    Handoff.canonicalGovernedLegalWorkflowSourceSemanticHandoff
  ≡ LegalSource.canonicalGovernedLegalWorkflowSourceGenealogyHandoff
legalSourceHandoffIsCanonical = refl

distilledReceiptIsCanonical :
  Handoff.distilledNonPromotionReceipt
    Handoff.canonicalGovernedLegalWorkflowSourceSemanticHandoff
  ≡ Distilled.canonicalPNFDistilledReuseZKPReceipt
distilledReceiptIsCanonical = refl

sharedLexemeStillDoesNotCreateSemanticIdentity :
  Distilled.sharedLexemeCreatesSemanticIdentity
    (Handoff.distilledNonPromotionReceipt
      Handoff.canonicalGovernedLegalWorkflowSourceSemanticHandoff)
  ≡ false
sharedLexemeStillDoesNotCreateSemanticIdentity = refl

diagnosticCheckStillDoesNotCreateTheoremPromotion :
  Distilled.diagnosticCheckCreatesTheoremPromotion
    (Handoff.distilledNonPromotionReceipt
      Handoff.canonicalGovernedLegalWorkflowSourceSemanticHandoff)
  ≡ false
diagnosticCheckStillDoesNotCreateTheoremPromotion = refl

sourceIdentifierStillDoesNotCreateProofAuthority :
  Distilled.sourceIdentifierCreatesProofAuthority
    (Handoff.distilledNonPromotionReceipt
      Handoff.canonicalGovernedLegalWorkflowSourceSemanticHandoff)
  ≡ false
sourceIdentifierStillDoesNotCreateProofAuthority = refl

esdMutationStillForbidden :
  Distilled.esdSurfaceMutationAllowed
    (Handoff.distilledNonPromotionReceipt
      Handoff.canonicalGovernedLegalWorkflowSourceSemanticHandoff)
  ≡ false
esdMutationStillForbidden = refl

unifierHandoffIsCanonical :
  Unifier.unifierGovernedLegalWorkflowSourceSemanticHandoff
  ≡ Handoff.canonicalGovernedLegalWorkflowSourceSemanticHandoff
unifierHandoffIsCanonical = refl
