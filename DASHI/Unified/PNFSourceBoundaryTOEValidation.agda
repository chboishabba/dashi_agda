module DASHI.Unified.PNFSourceBoundaryTOEValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Unified.PNFSourceBoundaryTOEExact as Boundary
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier

gluingFacadeExact :
  TOE.gluingProxyDoesNotProveTrueLinearity
  ≡ Boundary.gluingProxyDoesNotProveTrueLinearity
gluingFacadeExact = refl

selfAdjointFacadeExact :
  Unifier.selfAdjointProxyDoesNotProveFiniteTheorem
  ≡ Boundary.selfAdjointProxyDoesNotProveFiniteTheorem
selfAdjointFacadeExact = refl

dominationFacadeExact :
  TOE.dominationProxyDoesNotProveHamiltonianTheorem
  ≡ Unifier.dominationProxyDoesNotProveHamiltonianTheorem
dominationFacadeExact = refl

fungalFacadeExact :
  TOE.fungalNetworkClaimsRequireSpeciesEvidence
  ≡ Unifier.fungalNetworkClaimsRequireSpeciesEvidence
fungalFacadeExact = refl

sourceAtlasFacadeExact :
  TOE.sourceAtlasContainsTenRecords
  ≡ Unifier.sourceAtlasContainsTenRecords
sourceAtlasFacadeExact = refl
