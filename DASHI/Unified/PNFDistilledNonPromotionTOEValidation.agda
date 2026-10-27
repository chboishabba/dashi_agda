module DASHI.Unified.PNFDistilledNonPromotionTOEValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.PNFSourceBoundaryTOEValidation
import DASHI.Unified.PNFDistilledNonPromotionTOEExact as Distilled
import DASHI.Unifier as Unifier

unifierUsesCanonicalPNFDistilledZKPReceipt :
  Unifier.toePNFDistilledReuseZKPReceipt
  ≡
  Distilled.canonicalPNFDistilledReuseZKPReceipt
unifierUsesCanonicalPNFDistilledZKPReceipt =
  refl

sharedLexemeDoesNotCreateSemanticIdentity :
  Distilled.sharedLexemeCreatesSemanticIdentity
    Unifier.toePNFDistilledReuseZKPReceipt
  ≡ false
sharedLexemeDoesNotCreateSemanticIdentity =
  refl

diagnosticCheckDoesNotCreateTheoremPromotion :
  Distilled.diagnosticCheckCreatesTheoremPromotion
    Unifier.toePNFDistilledReuseZKPReceipt
  ≡ false
diagnosticCheckDoesNotCreateTheoremPromotion =
  refl

sourceIdentifierDoesNotCreateProofAuthority :
  Distilled.sourceIdentifierCreatesProofAuthority
    Unifier.toePNFDistilledReuseZKPReceipt
  ≡ false
sourceIdentifierDoesNotCreateProofAuthority =
  refl

esdMutationRemainsForbidden :
  Distilled.esdSurfaceMutationAllowed
    Unifier.toePNFDistilledReuseZKPReceipt
  ≡ false
esdMutationRemainsForbidden =
  refl
