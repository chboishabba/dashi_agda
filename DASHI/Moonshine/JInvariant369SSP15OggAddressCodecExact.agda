module DASHI.Moonshine.JInvariant369SSP15OggAddressCodecExact where

------------------------------------------------------------------------
-- SSP15 = THE FIFTEEN OGG / MONSTER PRIME LANES
--
-- The exact Ogg address p = 9 q + r is not merely a coarse observer.
-- Restricted to the fifteen Ogg primes it gives a concrete 15-way address
-- code.  This module makes that identification executable and proves both
-- round trips.
--
-- Complement mode / binary phase are downstream observations of this exact
-- lane.  Their collisions do not identify SSP15 lanes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Biology.OggPrimeNonaryAddressExact as Address
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

SSP15Lane : Set
SSP15Lane = Lane.MonsterPrimeLane

data SSP15OggAddress15 : Set where
  a02 a03 a05 a07 a11 a13 a17 a19 : SSP15OggAddress15
  a23 a29 a31 a41 a47 a59 a71 : SSP15OggAddress15

addressCoarseSheets : SSP15OggAddress15 → Nat
addressCoarseSheets a02 = 0
addressCoarseSheets a03 = 0
addressCoarseSheets a05 = 0
addressCoarseSheets a07 = 0
addressCoarseSheets a11 = 1
addressCoarseSheets a13 = 1
addressCoarseSheets a17 = 1
addressCoarseSheets a19 = 2
addressCoarseSheets a23 = 2
addressCoarseSheets a29 = 3
addressCoarseSheets a31 = 3
addressCoarseSheets a41 = 4
addressCoarseSheets a47 = 5
addressCoarseSheets a59 = 6
addressCoarseSheets a71 = 7

addressRemainder : SSP15OggAddress15 → Nat
addressRemainder a02 = 2
addressRemainder a03 = 3
addressRemainder a05 = 5
addressRemainder a07 = 7
addressRemainder a11 = 2
addressRemainder a13 = 4
addressRemainder a17 = 8
addressRemainder a19 = 1
addressRemainder a23 = 5
addressRemainder a29 = 2
addressRemainder a31 = 4
addressRemainder a41 = 5
addressRemainder a47 = 2
addressRemainder a59 = 5
addressRemainder a71 = 8

addressValue : SSP15OggAddress15 → Nat
addressValue address =
  addressCoarseSheets address * 9 + addressRemainder address

addressFromSSP15Lane : SSP15Lane → SSP15OggAddress15
addressFromSSP15Lane Lane.p2 = a02
addressFromSSP15Lane Lane.p3 = a03
addressFromSSP15Lane Lane.p5 = a05
addressFromSSP15Lane Lane.p7 = a07
addressFromSSP15Lane Lane.p11 = a11
addressFromSSP15Lane Lane.p13 = a13
addressFromSSP15Lane Lane.p17 = a17
addressFromSSP15Lane Lane.p19 = a19
addressFromSSP15Lane Lane.p23 = a23
addressFromSSP15Lane Lane.p29 = a29
addressFromSSP15Lane Lane.p31 = a31
addressFromSSP15Lane Lane.p41 = a41
addressFromSSP15Lane Lane.p47 = a47
addressFromSSP15Lane Lane.p59 = a59
addressFromSSP15Lane Lane.p71 = a71

ssp15LaneFromAddress : SSP15OggAddress15 → SSP15Lane
ssp15LaneFromAddress a02 = Lane.p2
ssp15LaneFromAddress a03 = Lane.p3
ssp15LaneFromAddress a05 = Lane.p5
ssp15LaneFromAddress a07 = Lane.p7
ssp15LaneFromAddress a11 = Lane.p11
ssp15LaneFromAddress a13 = Lane.p13
ssp15LaneFromAddress a17 = Lane.p17
ssp15LaneFromAddress a19 = Lane.p19
ssp15LaneFromAddress a23 = Lane.p23
ssp15LaneFromAddress a29 = Lane.p29
ssp15LaneFromAddress a31 = Lane.p31
ssp15LaneFromAddress a41 = Lane.p41
ssp15LaneFromAddress a47 = Lane.p47
ssp15LaneFromAddress a59 = Lane.p59
ssp15LaneFromAddress a71 = Lane.p71

laneAfterAddress :
  (lane : SSP15Lane) →
  ssp15LaneFromAddress (addressFromSSP15Lane lane) ≡ lane
laneAfterAddress Lane.p2 = refl
laneAfterAddress Lane.p3 = refl
laneAfterAddress Lane.p5 = refl
laneAfterAddress Lane.p7 = refl
laneAfterAddress Lane.p11 = refl
laneAfterAddress Lane.p13 = refl
laneAfterAddress Lane.p17 = refl
laneAfterAddress Lane.p19 = refl
laneAfterAddress Lane.p23 = refl
laneAfterAddress Lane.p29 = refl
laneAfterAddress Lane.p31 = refl
laneAfterAddress Lane.p41 = refl
laneAfterAddress Lane.p47 = refl
laneAfterAddress Lane.p59 = refl
laneAfterAddress Lane.p71 = refl

addressAfterLane :
  (address : SSP15OggAddress15) →
  addressFromSSP15Lane (ssp15LaneFromAddress address) ≡ address
addressAfterLane a02 = refl
addressAfterLane a03 = refl
addressAfterLane a05 = refl
addressAfterLane a07 = refl
addressAfterLane a11 = refl
addressAfterLane a13 = refl
addressAfterLane a17 = refl
addressAfterLane a19 = refl
addressAfterLane a23 = refl
addressAfterLane a29 = refl
addressAfterLane a31 = refl
addressAfterLane a41 = refl
addressAfterLane a47 = refl
addressAfterLane a59 = refl
addressAfterLane a71 = refl

addressValueIsSSP15Prime :
  (lane : SSP15Lane) →
  addressValue (addressFromSSP15Lane lane)
  ≡ Lane.monsterPrimeLaneToNat lane
addressValueIsSSP15Prime Lane.p2 = refl
addressValueIsSSP15Prime Lane.p3 = refl
addressValueIsSSP15Prime Lane.p5 = refl
addressValueIsSSP15Prime Lane.p7 = refl
addressValueIsSSP15Prime Lane.p11 = refl
addressValueIsSSP15Prime Lane.p13 = refl
addressValueIsSSP15Prime Lane.p17 = refl
addressValueIsSSP15Prime Lane.p19 = refl
addressValueIsSSP15Prime Lane.p23 = refl
addressValueIsSSP15Prime Lane.p29 = refl
addressValueIsSSP15Prime Lane.p31 = refl
addressValueIsSSP15Prime Lane.p41 = refl
addressValueIsSSP15Prime Lane.p47 = refl
addressValueIsSSP15Prime Lane.p59 = refl
addressValueIsSSP15Prime Lane.p71 = refl

codecCoordinatesAgreeWithCanonicalAddress :
  (lane : SSP15Lane) →
  (addressCoarseSheets (addressFromSSP15Lane lane)
    ≡ Address.coarseSheets (Address.nonaryOggAddress lane))
  ×
  (addressRemainder (addressFromSSP15Lane lane)
    ≡ Address.remainder (Address.nonaryOggAddress lane))
codecCoordinatesAgreeWithCanonicalAddress Lane.p2 = refl , refl
codecCoordinatesAgreeWithCanonicalAddress Lane.p3 = refl , refl
codecCoordinatesAgreeWithCanonicalAddress Lane.p5 = refl , refl
codecCoordinatesAgreeWithCanonicalAddress Lane.p7 = refl , refl
codecCoordinatesAgreeWithCanonicalAddress Lane.p11 = refl , refl
codecCoordinatesAgreeWithCanonicalAddress Lane.p13 = refl , refl
codecCoordinatesAgreeWithCanonicalAddress Lane.p17 = refl , refl
codecCoordinatesAgreeWithCanonicalAddress Lane.p19 = refl , refl
codecCoordinatesAgreeWithCanonicalAddress Lane.p23 = refl , refl
codecCoordinatesAgreeWithCanonicalAddress Lane.p29 = refl , refl
codecCoordinatesAgreeWithCanonicalAddress Lane.p31 = refl , refl
codecCoordinatesAgreeWithCanonicalAddress Lane.p41 = refl , refl
codecCoordinatesAgreeWithCanonicalAddress Lane.p47 = refl , refl
codecCoordinatesAgreeWithCanonicalAddress Lane.p59 = refl , refl
codecCoordinatesAgreeWithCanonicalAddress Lane.p71 = refl , refl

record SSP15OggAddressCodecBoundary : Set where
  constructor ssp15-ogg-address-codec-boundary
  field
    ssp15CarrierIsOggPrimeCarrier : Bool
    exactAddressCarrierHasFifteenCases : Bool
    exactAddressDecodesSSP15Lane : Bool
    laneAddressRoundTripPaid : Bool
    addressLaneRoundTripPaid : Bool
    exactAddressAgreesWithCanonicalNonaryProducer : Bool
    coarseModeOrientationIsOnlyDerivedObserver : Bool

open SSP15OggAddressCodecBoundary public

canonicalSSP15OggAddressCodecBoundary :
  SSP15OggAddressCodecBoundary
canonicalSSP15OggAddressCodecBoundary =
  ssp15-ogg-address-codec-boundary
    true true true true true true true
