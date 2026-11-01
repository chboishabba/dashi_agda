module DASHI.Moonshine.JInvariant369SSP15OggAddressRoot369BidiExact where

------------------------------------------------------------------------
-- EXACT OGG ADDRESS <-> ROOT 369 REFINEMENT
--
-- Branch-local capstone for PR #1053.
--
-- This composes the authoritative exact SSP15/Ogg address carrier with the
-- repository's depth-zero 369 refinement carrier.  The bridge between the two
-- prime datatypes is explicit constructor-by-constructor.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Data.Empty using (⊥)

import DASHI.Moonshine.JInvariant369SSP15OggAddressCodecExact as Address
import DASHI.Moonshine.JInvariant369SSP15OggAddressPhaseOrbitBidiExact as Phase
import DASHI.Foundations.SSPPrimeLane369Refinement as Ref
import DASHI.TrackedPrimes as TP

Root369Refinement : Set
Root369Refinement =
  Ref.SSPPrimeLane369Refinement zero

addressToTracked :
  Address.SSP15OggAddress15 ->
  TP.SSP
addressToTracked Address.a02 = TP.p2
addressToTracked Address.a03 = TP.p3
addressToTracked Address.a05 = TP.p5
addressToTracked Address.a07 = TP.p7
addressToTracked Address.a11 = TP.p11
addressToTracked Address.a13 = TP.p13
addressToTracked Address.a17 = TP.p17
addressToTracked Address.a19 = TP.p19
addressToTracked Address.a23 = TP.p23
addressToTracked Address.a29 = TP.p29
addressToTracked Address.a31 = TP.p31
addressToTracked Address.a41 = TP.p41
addressToTracked Address.a47 = TP.p47
addressToTracked Address.a59 = TP.p59
addressToTracked Address.a71 = TP.p71

trackedToAddress :
  TP.SSP ->
  Address.SSP15OggAddress15
trackedToAddress TP.p2 = Address.a02
trackedToAddress TP.p3 = Address.a03
trackedToAddress TP.p5 = Address.a05
trackedToAddress TP.p7 = Address.a07
trackedToAddress TP.p11 = Address.a11
trackedToAddress TP.p13 = Address.a13
trackedToAddress TP.p17 = Address.a17
trackedToAddress TP.p19 = Address.a19
trackedToAddress TP.p23 = Address.a23
trackedToAddress TP.p29 = Address.a29
trackedToAddress TP.p31 = Address.a31
trackedToAddress TP.p41 = Address.a41
trackedToAddress TP.p47 = Address.a47
trackedToAddress TP.p59 = Address.a59
trackedToAddress TP.p71 = Address.a71

addressTrackedRoundTrip :
  (address : Address.SSP15OggAddress15) ->
  trackedToAddress (addressToTracked address) ≡ address
addressTrackedRoundTrip Address.a02 = refl
addressTrackedRoundTrip Address.a03 = refl
addressTrackedRoundTrip Address.a05 = refl
addressTrackedRoundTrip Address.a07 = refl
addressTrackedRoundTrip Address.a11 = refl
addressTrackedRoundTrip Address.a13 = refl
addressTrackedRoundTrip Address.a17 = refl
addressTrackedRoundTrip Address.a19 = refl
addressTrackedRoundTrip Address.a23 = refl
addressTrackedRoundTrip Address.a29 = refl
addressTrackedRoundTrip Address.a31 = refl
addressTrackedRoundTrip Address.a41 = refl
addressTrackedRoundTrip Address.a47 = refl
addressTrackedRoundTrip Address.a59 = refl
addressTrackedRoundTrip Address.a71 = refl

trackedAddressRoundTrip :
  (prime : TP.SSP) ->
  addressToTracked (trackedToAddress prime) ≡ prime
trackedAddressRoundTrip TP.p2 = refl
trackedAddressRoundTrip TP.p3 = refl
trackedAddressRoundTrip TP.p5 = refl
trackedAddressRoundTrip TP.p7 = refl
trackedAddressRoundTrip TP.p11 = refl
trackedAddressRoundTrip TP.p13 = refl
trackedAddressRoundTrip TP.p17 = refl
trackedAddressRoundTrip TP.p19 = refl
trackedAddressRoundTrip TP.p23 = refl
trackedAddressRoundTrip TP.p29 = refl
trackedAddressRoundTrip TP.p31 = refl
trackedAddressRoundTrip TP.p41 = refl
trackedAddressRoundTrip TP.p47 = refl
trackedAddressRoundTrip TP.p59 = refl
trackedAddressRoundTrip TP.p71 = refl

addressToRoot369 :
  Address.SSP15OggAddress15 ->
  Root369Refinement
addressToRoot369 address =
  Ref.mkSSPPrimeLane369Refinement
    (addressToTracked address)
    Ref.root

root369ToAddress :
  Root369Refinement ->
  Address.SSP15OggAddress15
root369ToAddress refinement =
  trackedToAddress (Ref.primeLane refinement)

addressRoot369RoundTrip :
  (address : Address.SSP15OggAddress15) ->
  root369ToAddress (addressToRoot369 address)
  ≡ address
addressRoot369RoundTrip address =
  addressTrackedRoundTrip address

root369AddressRoundTrip :
  (refinement : Root369Refinement) ->
  addressToRoot369 (root369ToAddress refinement)
  ≡ refinement
root369AddressRoundTrip
  (Ref.mkSSPPrimeLane369Refinement prime Ref.root)
  rewrite trackedAddressRoundTrip prime = refl

------------------------------------------------------------------------
-- Compose the existing phase-orbit presentation through the exact address.
------------------------------------------------------------------------

phaseOrbitToRoot369 :
  Phase.PhaseOrbit15 ->
  Root369Refinement
phaseOrbitToRoot369 state =
  addressToRoot369 (Phase.phaseOrbitToAddress state)

root369ToPhaseOrbit :
  Root369Refinement ->
  Phase.PhaseOrbit15
root369ToPhaseOrbit refinement =
  Phase.addressToPhaseOrbit (root369ToAddress refinement)

phaseOrbitRoot369RoundTrip :
  (state : Phase.PhaseOrbit15) ->
  root369ToPhaseOrbit (phaseOrbitToRoot369 state)
  ≡ state
phaseOrbitRoot369RoundTrip state
  rewrite addressRoot369RoundTrip (Phase.phaseOrbitToAddress state) =
  Phase.phaseOrbitAddressRoundTrip state

root369PhaseOrbitRoundTrip :
  (refinement : Root369Refinement) ->
  phaseOrbitToRoot369 (root369ToPhaseOrbit refinement)
  ≡ refinement
root369PhaseOrbitRoundTrip refinement
  rewrite Phase.addressPhaseOrbitRoundTrip (root369ToAddress refinement) =
  root369AddressRoundTrip refinement

------------------------------------------------------------------------
-- Firewall.
------------------------------------------------------------------------

data Root369AddressIsAnalyticPAdicCoordinate : Set where
data ThreeByFivePresentationIsRoot369IntrinsicFactorization : Set where

root369AddressDoesNotCreateAnalyticPAdicCoordinate :
  Root369AddressIsAnalyticPAdicCoordinate -> ⊥
root369AddressDoesNotCreateAnalyticPAdicCoordinate ()

threeByFiveNotPromotedToIntrinsic369Factorization :
  ThreeByFivePresentationIsRoot369IntrinsicFactorization -> ⊥
threeByFiveNotPromotedToIntrinsic369Factorization ()

record SSP15OggAddressRoot369BidiBoundary : Set where
  constructor ssp15-ogg-address-root369-bidi-boundary
  field
    exactAddressTrackedPrimeBidiPaid : Bool
    exactAddressRoot369BidiPaid : Bool
    phaseOrbitRoot369BidiPaid : Bool
    rootAddressUniquenessUsed : Bool
    analyticPAdicCoordinateConstructed : Bool
    threeByFiveIsIntrinsic369Factorization : Bool

canonicalSSP15OggAddressRoot369BidiBoundary :
  SSP15OggAddressRoot369BidiBoundary
canonicalSSP15OggAddressRoot369BidiBoundary =
  ssp15-ogg-address-root369-bidi-boundary
    true true true true false false
