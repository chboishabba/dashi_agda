module DASHI.Foundations.PrimeLaneUnitActionQuotient where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)

open import DASHI.Foundations.SSPPrimeLaneUnitAction as Action using
  ( SSPPrimeLaneUnitActionProfile
  ; canonicalGeneratorStep
  ; primeLaneUnitActionProfile
  ; normalizedUnitStep
  )
open import DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge as Phase using
  ( SSPPrimeLane369PhaseBridge
  ; primeLane369PhaseBridge
  ; unitOrder
  )
open import DASHI.TrackedPrimes using (SSP; p7; p11)

------------------------------------------------------------------------
-- Prime-lane quotient-action surface.
--
-- The shape is intentionally finite and candidate-only.  It records the
-- carrier label/order, the identity element, the canonical step projection,
-- and the receipts needed for the local p7/C6 and follow-on p11/C10 stories.

record PrimeLaneQuotientCarrier : Set where
  constructor mkPrimeLaneQuotientCarrier
  field
    carrierLabel :
      String

    carrierOrder :
      Nat

    identityElement :
      Nat

    identityElementIsZero :
      identityElement ≡ zero

    stepProjection :
      Nat → Nat

    identityProjection :
      Nat

    identityProjectionIsProjection :
      identityProjection ≡ stepProjection identityElement

    canonicalGeneratorProjection :
      Nat

    canonicalGeneratorProjectionIsProjection :
      canonicalGeneratorProjection ≡ stepProjection canonicalGeneratorStep

open PrimeLaneQuotientCarrier public

record PrimeLaneCandidateOnlyAuthority : Set where
  constructor mkPrimeLaneCandidateOnlyAuthority
  field
    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    coreAuthorityBit :
      Bool

    coreAuthorityBitIsTrue :
      coreAuthorityBit ≡ true

    coreReceiptBit :
      Bool

    coreReceiptBitIsTrue :
      coreReceiptBit ≡ true

open PrimeLaneCandidateOnlyAuthority public

record PrimeLaneUnitActionQuotientSurface : Set where
  constructor mkPrimeLaneUnitActionQuotientSurface
  field
    primeIdentity :
      SSP

    carrier :
      PrimeLaneQuotientCarrier

    phaseBridge :
      SSPPrimeLane369PhaseBridge

    phaseBridgeIsCanonical :
      phaseBridge ≡ primeLane369PhaseBridge primeIdentity

    actionReceipt :
      SSPPrimeLaneUnitActionProfile

    actionReceiptIsCanonical :
      actionReceipt ≡
      primeLaneUnitActionProfile primeIdentity canonicalGeneratorStep

    candidateAuthority :
      PrimeLaneCandidateOnlyAuthority

    carrierOrderMatchesPhaseBridge :
      carrierOrder carrier ≡ unitOrder phaseBridge

open PrimeLaneUnitActionQuotientSurface public

------------------------------------------------------------------------
-- Canonical p7/C6 and p11/C10 surfaces.

p7C6PrimeLaneQuotientCarrier : PrimeLaneQuotientCarrier
p7C6PrimeLaneQuotientCarrier =
  mkPrimeLaneQuotientCarrier
    "p7/C6"
    6
    zero
    refl
    (normalizedUnitStep p7)
    (normalizedUnitStep p7 zero)
    refl
    (normalizedUnitStep p7 canonicalGeneratorStep)
    refl

p11C10PrimeLaneQuotientCarrier : PrimeLaneQuotientCarrier
p11C10PrimeLaneQuotientCarrier =
  mkPrimeLaneQuotientCarrier
    "p11/C10"
    10
    zero
    refl
    (normalizedUnitStep p11)
    (normalizedUnitStep p11 zero)
    refl
    (normalizedUnitStep p11 canonicalGeneratorStep)
    refl

p7CandidateOnlyAuthority : PrimeLaneCandidateOnlyAuthority
p7CandidateOnlyAuthority =
  mkPrimeLaneCandidateOnlyAuthority
    true
    refl
    true
    refl
    true
    refl

p11CandidateOnlyAuthority : PrimeLaneCandidateOnlyAuthority
p11CandidateOnlyAuthority =
  mkPrimeLaneCandidateOnlyAuthority
    true
    refl
    true
    refl
    true
    refl

p7C6PrimeLaneUnitActionQuotientSurface :
  PrimeLaneUnitActionQuotientSurface
p7C6PrimeLaneUnitActionQuotientSurface =
  mkPrimeLaneUnitActionQuotientSurface
    p7
    p7C6PrimeLaneQuotientCarrier
    (primeLane369PhaseBridge p7)
    refl
    (primeLaneUnitActionProfile p7 canonicalGeneratorStep)
    refl
    p7CandidateOnlyAuthority
    refl

p11C10PrimeLaneUnitActionQuotientSurface :
  PrimeLaneUnitActionQuotientSurface
p11C10PrimeLaneUnitActionQuotientSurface =
  mkPrimeLaneUnitActionQuotientSurface
    p11
    p11C10PrimeLaneQuotientCarrier
    (primeLane369PhaseBridge p11)
    refl
    (primeLaneUnitActionProfile p11 canonicalGeneratorStep)
    refl
    p11CandidateOnlyAuthority
    refl

