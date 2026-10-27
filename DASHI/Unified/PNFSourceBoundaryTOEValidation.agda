module DASHI.Unified.PNFSourceBoundaryTOEValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.PNFSourceBoundaryTOEExact as Boundary
import DASHI.Unifier as Unifier

unifierUsesCanonicalPNFSourceBoundaryReceipt :
  Unifier.toePNFSourceBoundaryReceipt
  ≡
  Boundary.canonicalPNFSourceBoundaryTOEReceipt
unifierUsesCanonicalPNFSourceBoundaryReceipt =
  refl

gluingFacadeExact :
  Unifier.toePNFGluingProxyDoesNotProveTrueLinearity
  ≡
  Boundary.gluingProxyDoesNotProveTrueLinearity
gluingFacadeExact =
  refl

selfAdjointFacadeExact :
  Unifier.toePNFSelfAdjointProxyDoesNotProveFiniteTheorem
  ≡
  Boundary.selfAdjointProxyDoesNotProveFiniteTheorem
selfAdjointFacadeExact =
  refl

dominationFacadeExact :
  Unifier.toePNFDominationProxyDoesNotProveHamiltonianTheorem
  ≡
  Boundary.dominationProxyDoesNotProveHamiltonianTheorem
dominationFacadeExact =
  refl

fungalFacadeExact :
  Unifier.toePNFFungalNetworkClaimsRequireSpeciesEvidence
  ≡
  Boundary.fungalNetworkClaimsRequireSpeciesEvidence
fungalFacadeExact =
  refl

kluverCobwebFacadeExact :
  Unifier.toePNFKluverCobwebForm
  ≡
  Boundary.kluverCobwebForm
kluverCobwebFacadeExact =
  refl

webIdentifierFacadeExact :
  Unifier.toePNFPsychogeographyWebIdentifierKind
  ≡
  Boundary.psychogeographyWebIdentifierKind
webIdentifierFacadeExact =
  refl
