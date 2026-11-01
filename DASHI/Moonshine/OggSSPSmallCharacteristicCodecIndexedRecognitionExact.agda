module DASHI.Moonshine.OggSSPSmallCharacteristicCodecIndexedRecognitionExact where

------------------------------------------------------------------------
-- EXACT-CODEC-INDEXED SMALL-CHARACTERISTIC RECOGNITION
--
-- The SSP15/Ogg lane is not an open recognition problem:
--
--   exact Ogg address p = 9q+r  <->  one of the fifteen Ogg prime lanes.
--
-- What remains open at p=2 and p=3 is the arithmetic residual-groupoid fibre.
-- Therefore any arithmetic recognition object must first carry an exact Ogg
-- address witness fixing its prime lane.  The lossy coarse
-- (complement-mode,binary-orientation) observer is not accepted as a lane key.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.JInvariant369SSP15OggAddressCodecExact as Codec
import DASHI.Moonshine.JInvariant369OggAddressSSP15NoGoExact as Coarse
import DASHI.Moonshine.OggSSPArithmeticResidualGroupoidRecognitionFunctorExact as Recognition

------------------------------------------------------------------------
-- 1. Exact lane key.
------------------------------------------------------------------------

record ExactOggLaneKey : Set where
  constructor exact-ogg-lane-key
  field
    lane : Lane.MonsterPrimeLane
    address : Codec.SSP15OggAddress15
    addressIsCanonical :
      address ≡ Codec.addressFromSSP15Lane lane

open ExactOggLaneKey public

decodeExactLaneKey : ExactOggLaneKey → Lane.MonsterPrimeLane
decodeExactLaneKey key = Codec.ssp15LaneFromAddress (address key)

decodeExactLaneKeyCorrect :
  (key : ExactOggLaneKey) →
  decodeExactLaneKey key ≡ lane key
decodeExactLaneKeyCorrect key
  rewrite addressIsCanonical key =
  Codec.laneAfterAddress (lane key)

exactLaneKeyAddressDeterminesLane :
  (left right : ExactOggLaneKey) →
  Codec.addressCoordinates (address left)
  ≡ Codec.addressCoordinates (address right) →
  lane left ≡ lane right
exactLaneKeyAddressDeterminesLane left right same =
  trans
    (sym (decodeExactLaneKeyCorrect left))
    (trans
      (cong Codec.ssp15LaneFromAddress
        (Codec.addressCoordinatesInjective
          (address left)
          (address right)
          same))
      (decodeExactLaneKeyCorrect right))

------------------------------------------------------------------------
-- 2. Canonical small-characteristic lane keys.
------------------------------------------------------------------------

p2LaneKey : ExactOggLaneKey
p2LaneKey =
  exact-ogg-lane-key
    Lane.p2
    (Codec.addressFromSSP15Lane Lane.p2)
    refl

p3LaneKey : ExactOggLaneKey
p3LaneKey =
  exact-ogg-lane-key
    Lane.p3
    (Codec.addressFromSSP15Lane Lane.p3)
    refl

p2KeyDecodesToP2 :
  decodeExactLaneKey p2LaneKey ≡ Lane.p2
p2KeyDecodesToP2 = Codec.laneAfterAddress Lane.p2

p3KeyDecodesToP3 :
  decodeExactLaneKey p3LaneKey ≡ Lane.p3
p3KeyDecodesToP3 = Codec.laneAfterAddress Lane.p3

data P2EqualsP3Lane : Set where

p2AndP3LanesDistinct :
  Lane.p2 ≡ Lane.p3 → ⊥
p2AndP3LanesDistinct ()

p2AndP3ExactAddressesDistinct :
  address p2LaneKey ≡ address p3LaneKey → ⊥
p2AndP3ExactAddressesDistinct same =
  p2AndP3LanesDistinct
    (trans
      (sym p2KeyDecodesToP2)
      (trans
        (cong Codec.ssp15LaneFromAddress same)
        p3KeyDecodesToP3))

------------------------------------------------------------------------
-- 3. Coarse observer is explicitly not an admissible universal lane key.
------------------------------------------------------------------------

record CoarseOggLaneKey : Set where
  constructor coarse-ogg-lane-key
  field
    coarse : Coarse.OggAddressCoarse10

open CoarseOggLaneKey public

data CoarseObserverUniversallyDeterminesSSP15Lane : Set where

coarseObserverCannotUniversallyDetermineSSP15Lane :
  CoarseObserverUniversallyDeterminesSSP15Lane → ⊥
coarseObserverCannotUniversallyDetermineSSP15Lane ()

p2AndP11CoarseCollision :
  Coarse.addressCoarse10 Lane.p2
  ≡ Coarse.addressCoarse10 Lane.p11
p2AndP11CoarseCollision =
  Coarse.p2AndP11HaveSameAddressCoarse10

------------------------------------------------------------------------
-- 4. Recognition request is indexed by the exact prime lane.
--
-- This record does not construct the arithmetic groupoid.  It prevents a
-- future construction from proving only an unindexed residual-count match and
-- then silently assigning it to p=2 or p=3.
------------------------------------------------------------------------

data SmallCharacteristicLane : Set where
  p2 : SmallCharacteristicLane
  p3 : SmallCharacteristicLane

laneKey : SmallCharacteristicLane → ExactOggLaneKey
laneKey p2 = p2LaneKey
laneKey p3 = p3LaneKey

data SmallCharacteristicRecognitionResidual : SmallCharacteristicLane → Set where
  arithmeticSourceGroupoidMissing :
    (which : SmallCharacteristicLane) →
    SmallCharacteristicRecognitionResidual which

currentP2Residual : SmallCharacteristicRecognitionResidual p2
currentP2Residual = arithmeticSourceGroupoidMissing p2

currentP3Residual : SmallCharacteristicRecognitionResidual p3
currentP3Residual = arithmeticSourceGroupoidMissing p3

record CodecIndexedRecognitionBoundary : Set where
  constructor codec-indexed-recognition-boundary
  field
    exactOggAddressCodecReused : Bool
    exactAddressDeterminesSSP15Lane : Bool
    p2AndP3ExactLaneKeysConstructed : Bool
    coarseObserverRejectedAsUniversalLaneKey : Bool
    recognitionResidualIndexedByExactLane : Bool
    arithmeticP2SourceGroupoidConstructed : Bool
    arithmeticP3SourceGroupoidConstructed : Bool

canonicalCodecIndexedRecognitionBoundary :
  CodecIndexedRecognitionBoundary
canonicalCodecIndexedRecognitionBoundary =
  codec-indexed-recognition-boundary
    true true true true true false false
