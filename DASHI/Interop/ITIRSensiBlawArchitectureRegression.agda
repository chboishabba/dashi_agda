module DASHI.Interop.ITIRSensiBlawArchitectureRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.ITIRActorIdentitySpine as ActorSpine
import DASHI.Interop.ITIRSensiBlawStreamlineArchitecture as Architecture
import DASHI.Interop.PolisITIRDeliberationBoundary as Polis
import DASHI.Interop.TiRCorderSensiBlawConnectorBoundary as TiRCSL

------------------------------------------------------------------------
-- Compact aggregate witness surface for the ITIR/SensiBlaw interop tranche.

actorSpineCanonical :
  ActorSpine.authorityBits ActorSpine.canonicalITIRActorIdentitySpine
  ≡ ActorSpine.canonicalActorIdentityAuthorityBits
actorSpineCanonical = refl

tiRCorderSensiBlawBoundaryCanonical :
  TiRCSL.tiRCorderAuthority
    TiRCSL.canonicalTiRCorderSensiBlawConnectorBoundary
  ≡ TiRCSL.canonicalTiRCorderAuthorityBits
tiRCorderSensiBlawBoundaryCanonical = refl

sensiBlawAuthorityCanonical :
  TiRCSL.sensiBlawAuthority
    TiRCSL.canonicalTiRCorderSensiBlawConnectorBoundary
  ≡ TiRCSL.canonicalSensiBlawAuthorityBits
sensiBlawAuthorityCanonical = refl

polisBoundaryCanonical :
  Polis.polisAuthority Polis.canonicalPolisITIRDeliberationBoundary
  ≡ Polis.canonicalPolisAuthorityBits
polisBoundaryCanonical = refl

itirDeliberationAuthorityCanonical :
  Polis.itirAuthority Polis.canonicalPolisITIRDeliberationBoundary
  ≡ Polis.canonicalITIRDeliberationAuthorityBits
itirDeliberationAuthorityCanonical = refl

architectureCanonical :
  Architecture.authorityBits
    Architecture.canonicalITIRSensiBlawStreamlineArchitecture
  ≡ Architecture.canonicalArchitectureAuthorityBits
architectureCanonical = refl
