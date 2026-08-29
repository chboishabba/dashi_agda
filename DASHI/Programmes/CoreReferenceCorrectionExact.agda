module DASHI.Programmes.CoreReferenceCorrectionExact where

open import DASHI.Core.Prelude

import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Programmes.BidirectionalSatelliteCorrectionExact as BIDI

------------------------------------------------------------------------
-- BIDI cut for dashiCORE.
--
-- The executable Python repository is a reference implementation, while the
-- Agda tree is the theorem owner.  Backend fingerprints are parity witnesses;
-- they are not semantic equality and cannot transport arbitrary claims.
------------------------------------------------------------------------

ReferenceImplementationBridge :
  ∀ {State Reference Formal Claim : Set} →
  (State → Reference) →
  (State → Formal) →
  (State → Claim) → Set₁
ReferenceImplementationBridge = BIDI.CorrectedSatelliteBridge

referenceImplementationReusesFormalClaim :
  ∀ {State Reference Formal Claim : Set}
    {reference : State → Reference}
    {formal : State → Formal}
    {claim : State → Claim} →
  ReferenceImplementationBridge reference formal claim →
  Transport.ClaimTransport reference claim
referenceImplementationReusesFormalClaim =
  BIDI.correctedSatelliteYieldsClaimTransport

FingerprintCollision :
  ∀ {State Fingerprint Claim : Set} →
  (State → Fingerprint) →
  (State → Claim) → Set
FingerprintCollision = Transport.ClaimNonTransportWitness

fingerprintCollisionBlocksSemanticPromotion :
  ∀ {State Fingerprint Claim : Set}
    {fingerprint : State → Fingerprint}
    {claim : State → Claim} →
  FingerprintCollision fingerprint claim →
  Transport.ClaimTransport fingerprint claim →
  ⊥
fingerprintCollisionBlocksSemanticPromotion =
  Transport.claimNonTransportWitnessBlocksTransport

record CoreReferenceCorrectionBoundary : Set where
  constructor coreReferenceCorrectionBoundary
  field
    backendFingerprintEqualityIsStateEquality : Bool
    backendFingerprintEqualityIsStateEqualityIsFalse :
      backendFingerprintEqualityIsStateEquality ≡ false

    referenceImplementationDefinesFormalSemanticsByItself : Bool
    referenceImplementationDefinesFormalSemanticsByItselfIsFalse :
      referenceImplementationDefinesFormalSemanticsByItself ≡ false

    commutingReferenceBridgeMayReuseAgdaClaims : Bool
    commutingReferenceBridgeMayReuseAgdaClaimsIsTrue :
      commutingReferenceBridgeMayReuseAgdaClaims ≡ true

    kernelIsAutomaticallyContractiveOrIdempotent : Bool
    kernelIsAutomaticallyContractiveOrIdempotentIsFalse :
      kernelIsAutomaticallyContractiveOrIdempotent ≡ false

canonicalCoreReferenceCorrectionBoundary : CoreReferenceCorrectionBoundary
canonicalCoreReferenceCorrectionBoundary =
  coreReferenceCorrectionBoundary
    false refl
    false refl
    true refl
    false refl
