module DASHI.Cognition.PNF.ObserverSeparationAuthorityBoundaryExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.ProofRelevantIdentityFibres as Identity
import DASHI.Core.ObserverRefinementLatticeExact as Observer

surfaceSeparationCannotCreateWorldIdentityAuthority :
  ∀ {State Value : Set}
    {observe : Observer.Observer State Value} →
  Observer.Separating observe →
  Identity.WorldCanonicalPermission Identity.surfaceLocal →
  ⊥
surfaceSeparationCannotCreateWorldIdentityAuthority separating =
  Identity.surfaceIdentityCannotClaimWorldIdentity

documentSeparationCannotCreateWorldIdentityAuthority :
  ∀ {State Value : Set}
    {observe : Observer.Observer State Value} →
  Observer.Separating observe →
  Identity.WorldCanonicalPermission Identity.documentDerived →
  ⊥
documentSeparationCannotCreateWorldIdentityAuthority separating =
  Identity.documentIdentityCannotClaimWorldIdentity

corpusSeparationCannotCreateWorldIdentityAuthority :
  ∀ {State Value : Set}
    {observe : Observer.Observer State Value} →
  Observer.Separating observe →
  Identity.WorldCanonicalPermission Identity.corpusDerived →
  ⊥
corpusSeparationCannotCreateWorldIdentityAuthority separating =
  Identity.corpusIdentityCannotClaimWorldIdentity

externalAuthorityRemainsSeparateWitness :
  Identity.WorldCanonicalPermission Identity.externalAuthority
externalAuthorityRemainsSeparateWitness =
  Identity.externalAuthorityMayNameWorldEntity

record ObserverSeparationAuthorityBoundary : Set where
  constructor observerSeparationAuthorityBoundary
  field
    separationIsCarrierRelative : Bool
    separationIsCarrierRelativeIsTrue : separationIsCarrierRelative ≡ true
    surfaceSeparationGrantsWorldIdentityAuthority : Bool
    surfaceSeparationGrantsWorldIdentityAuthorityIsFalse :
      surfaceSeparationGrantsWorldIdentityAuthority ≡ false
    documentSeparationGrantsWorldIdentityAuthority : Bool
    documentSeparationGrantsWorldIdentityAuthorityIsFalse :
      documentSeparationGrantsWorldIdentityAuthority ≡ false
    corpusSeparationGrantsWorldIdentityAuthority : Bool
    corpusSeparationGrantsWorldIdentityAuthorityIsFalse :
      corpusSeparationGrantsWorldIdentityAuthority ≡ false
    externalWorldIdentityAuthorityRequiresSeparateWitness : Bool
    externalWorldIdentityAuthorityRequiresSeparateWitnessIsTrue :
      externalWorldIdentityAuthorityRequiresSeparateWitness ≡ true

canonicalObserverSeparationAuthorityBoundary :
  ObserverSeparationAuthorityBoundary
canonicalObserverSeparationAuthorityBoundary =
  observerSeparationAuthorityBoundary
    true refl false refl false refl false refl true refl
