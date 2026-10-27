module DASHI.Unified.GovernedLegalWorkflowSourceSemanticTOERegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.GovernedLegalWorkflowSourceSemanticTOEExact as Handoff
import DASHI.Unified.GovernedLegalWorkflowSourceGenealogyTOEExact as LegalSource
import DASHI.Unified.PNFDistilledNonPromotionTOEExact as Distilled
import DASHI.Law.SensibLawAgdaFirstLegalRuntimeEverything as LegalRuntime
import DASHI.Governance.DomainPermeabilityAuthorityTransport as Domain
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

runtimeContractIsCanonical :
  Handoff.legalRuntimeContract
    Handoff.canonicalGovernedLegalWorkflowSourceSemanticHandoff
  ≡ LegalRuntime.canonicalAgdaFirstLegalRuntimeContract
runtimeContractIsCanonical = refl

domainTransportReceiptIsCanonical :
  Handoff.domainTransportReceipt
    Handoff.canonicalGovernedLegalWorkflowSourceSemanticHandoff
  ≡ Domain.canonicalDomainTransportReceipt
domainTransportReceiptIsCanonical = refl

runtimeSemanticsStillFailClosed :
  LegalRuntime.AgdaFirstLegalRuntimeContract.runtimeMayInventMissingFormalLegalSemantics
    (Handoff.legalRuntimeContract
      Handoff.canonicalGovernedLegalWorkflowSourceSemanticHandoff)
  ≡ false
runtimeSemanticsStillFailClosed = refl

sourceFollowAuthorityStillFailClosed :
  LegalRuntime.AgdaFirstLegalRuntimeContract.sourceFollowMayBecomeAuthorityByTransport
    (Handoff.legalRuntimeContract
      Handoff.canonicalGovernedLegalWorkflowSourceSemanticHandoff)
  ≡ false
sourceFollowAuthorityStillFailClosed = refl

representationAuthorityStillFailClosed :
  Domain.DomainTransportReceipt.representationEqualityCreatesLegalAuthority
    (Handoff.domainTransportReceipt
      Handoff.canonicalGovernedLegalWorkflowSourceSemanticHandoff)
  ≡ false
representationAuthorityStillFailClosed = refl

vendorAuthorityStillFailClosed :
  Domain.DomainTransportReceipt.vendorIdentityCreatesAuthority
    (Handoff.domainTransportReceipt
      Handoff.canonicalGovernedLegalWorkflowSourceSemanticHandoff)
  ≡ false
vendorAuthorityStillFailClosed = refl

targetDomainAuthorityWitnessStillRequired :
  Domain.DomainTransportReceipt.targetDomainNeedsOwnAuthorityWitness
    (Handoff.domainTransportReceipt
      Handoff.canonicalGovernedLegalWorkflowSourceSemanticHandoff)
  ≡ true
targetDomainAuthorityWitnessStillRequired = refl
