module DASHI.Unified.PNFDistilledNonPromotionTOEValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.PNFDistilledNonPromotionTOEExact as Bridge
import DASHI.Unifier as Unifier

unifierUsesCanonicalPNFDistilledBoundary :
  Unifier.toePNFDistilledNonPromotionBoundary
  ≡
  Bridge.canonicalPNFDistilledNonPromotionBoundary
unifierUsesCanonicalPNFDistilledBoundary =
  refl

unifierUsesCanonicalPNFDistilledZKPReceipt :
  Unifier.toePNFDistilledReuseZKPReceipt
  ≡
  Bridge.canonicalPNFDistilledReuseZKPReceipt
unifierUsesCanonicalPNFDistilledZKPReceipt =
  refl

gluingDiagnosticRemainsNonPromoting :
  Bridge.gluingDiagnosticPromotionIsFalse
    Unifier.toePNFDistilledNonPromotionBoundary
  ≡
  Bridge.gluingDiagnosticPromotionIsFalse
    Bridge.canonicalPNFDistilledNonPromotionBoundary
gluingDiagnosticRemainsNonPromoting =
  refl

selfAdjointDiagnosticRemainsNonPromoting :
  Bridge.selfAdjointDiagnosticPromotionIsFalse
    Unifier.toePNFDistilledNonPromotionBoundary
  ≡
  Bridge.selfAdjointDiagnosticPromotionIsFalse
    Bridge.canonicalPNFDistilledNonPromotionBoundary
selfAdjointDiagnosticRemainsNonPromoting =
  refl

dominationDiagnosticRemainsNonPromoting :
  Bridge.dominationDiagnosticPromotionIsFalse
    Unifier.toePNFDistilledNonPromotionBoundary
  ≡
  Bridge.dominationDiagnosticPromotionIsFalse
    Bridge.canonicalPNFDistilledNonPromotionBoundary
dominationDiagnosticRemainsNonPromoting =
  refl

fungalEvidenceRequirementRemainsTrue :
  Bridge.fungalWoodWebNeedsSpeciesEvidence
    Unifier.toePNFDistilledNonPromotionBoundary
  ≡
  Bridge.fungalWoodWebNeedsSpeciesEvidence
    Bridge.canonicalPNFDistilledNonPromotionBoundary
fungalEvidenceRequirementRemainsTrue =
  refl

sharedLexemeDoesNotCreateSemanticIdentity :
  Bridge.sharedLexemeCreatesSemanticIdentity
    Unifier.toePNFDistilledReuseZKPReceipt
  ≡ false
sharedLexemeDoesNotCreateSemanticIdentity =
  refl

diagnosticCheckDoesNotCreateTheoremPromotion :
  Bridge.diagnosticCheckCreatesTheoremPromotion
    Unifier.toePNFDistilledReuseZKPReceipt
  ≡ false
diagnosticCheckDoesNotCreateTheoremPromotion =
  refl

sourceIdentifierDoesNotCreateProofAuthority :
  Bridge.sourceIdentifierCreatesProofAuthority
    Unifier.toePNFDistilledReuseZKPReceipt
  ≡ false
sourceIdentifierDoesNotCreateProofAuthority =
  refl

esdMutationRemainsForbidden :
  Bridge.esdSurfaceMutationAllowed
    Unifier.toePNFDistilledReuseZKPReceipt
  ≡ false
esdMutationRemainsForbidden =
  refl
