module DASHI.Unified.PNFDistilledNonPromotionTOEValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.PNFSourceBoundaryTOEExact as Boundary
import DASHI.Unified.PNFDistilledNonPromotionTOEExact as Distilled
import DASHI.Unifier as Unifier

unifierUsesCanonicalPNFSourceBoundaryReceipt :
  Unifier.toePNFSourceBoundaryReceipt
  ≡
  Boundary.canonicalPNFSourceBoundaryTOEReceipt
unifierUsesCanonicalPNFSourceBoundaryReceipt =
  refl

unifierUsesCanonicalPNFDistilledZKPReceipt :
  Unifier.toePNFDistilledReuseZKPReceipt
  ≡
  Distilled.canonicalPNFDistilledReuseZKPReceipt
unifierUsesCanonicalPNFDistilledZKPReceipt =
  refl

unifierGluingFactIsCanonical :
  Unifier.toePNFGluingProxyDoesNotProveTrueLinearity
  ≡
  Boundary.gluingProxyDoesNotProveTrueLinearity
unifierGluingFactIsCanonical =
  refl

unifierSelfAdjointFactIsCanonical :
  Unifier.toePNFSelfAdjointProxyDoesNotProveFiniteTheorem
  ≡
  Boundary.selfAdjointProxyDoesNotProveFiniteTheorem
unifierSelfAdjointFactIsCanonical =
  refl

unifierDominationFactIsCanonical :
  Unifier.toePNFDominationProxyDoesNotProveHamiltonianTheorem
  ≡
  Boundary.dominationProxyDoesNotProveHamiltonianTheorem
unifierDominationFactIsCanonical =
  refl

unifierFungalEvidenceFactIsCanonical :
  Unifier.toePNFFungalNetworkClaimsRequireSpeciesEvidence
  ≡
  Boundary.fungalNetworkClaimsRequireSpeciesEvidence
unifierFungalEvidenceFactIsCanonical =
  refl

unifierKluverCobwebCoordinateIsCanonical :
  Unifier.toePNFKluverCobwebForm
  ≡
  Boundary.kluverCobwebForm
unifierKluverCobwebCoordinateIsCanonical =
  refl

unifierWebIdentifierCoordinateIsCanonical :
  Unifier.toePNFPsychogeographyWebIdentifierKind
  ≡
  Boundary.psychogeographyWebIdentifierKind
unifierWebIdentifierCoordinateIsCanonical =
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
