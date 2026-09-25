module DASHI.Moonshine.JInvariant369OggAddressResidualFibreExact where

------------------------------------------------------------------------
-- OGG ADDRESS OBSERVATION + LOSSLESS RESIDUAL FIBRE
--
-- The address law canonically exposes only
--
--   (complement mode , binary orientation).
--
-- The corrected SSP15 semantics keeps the full
--
--   (Monster/Ogg prime , internal SSP15 lane)
--
-- upstairs.  This module makes that architecture exact: the coarse address
-- value is an observation of the prime coordinate, while the full semantic
-- state is retained as residual data.  Forgetting the residual is genuinely
-- lossy; retaining it gives a definitional round trip.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.JInvariant369OggAddressSSP15NoGoExact as NoGo
import DASHI.Moonshine.JInvariant369SSP15PrimeInternalFibreExact as Fibre

------------------------------------------------------------------------
-- 1. Lossless observed state.
------------------------------------------------------------------------

AddressObservedPrimeInternal : Set
AddressObservedPrimeInternal =
  NoGo.OggAddressCoarse10 × Fibre.PrimeInternalCarrier

observeWithResidual :
  Fibre.PrimeInternalCarrier →
  AddressObservedPrimeInternal
observeWithResidual state =
  NoGo.addressCoarse10 (proj₁ state) , state

observedAddress :
  AddressObservedPrimeInternal →
  NoGo.OggAddressCoarse10
observedAddress = proj₁

residualPrimeInternal :
  AddressObservedPrimeInternal →
  Fibre.PrimeInternalCarrier
residualPrimeInternal = proj₂

recoverAfterObserve :
  (state : Fibre.PrimeInternalCarrier) →
  residualPrimeInternal (observeWithResidual state) ≡ state
recoverAfterObserve state = refl

addressObservationFactorsThroughPrime :
  (state : Fibre.PrimeInternalCarrier) →
  observedAddress (observeWithResidual state)
  ≡ NoGo.addressCoarse10 (proj₁ state)
addressObservationFactorsThroughPrime state = refl

------------------------------------------------------------------------
-- 2. The address observer intentionally forgets the internal SSP15 lane.
------------------------------------------------------------------------

p71NeutralAndCounterposedHaveSameObservedAddress :
  observedAddress (observeWithResidual Fibre.p71NeutralPair)
  ≡
  observedAddress (observeWithResidual Fibre.p71CounterposedPair)
p71NeutralAndCounterposedHaveSameObservedAddress = refl

p71ResidualStillDistinguishesTheStates :
  residualPrimeInternal (observeWithResidual Fibre.p71NeutralPair)
  ≡
  residualPrimeInternal (observeWithResidual Fibre.p71CounterposedPair)
  → ⊥
p71ResidualStillDistinguishesTheStates =
  Fibre.p71NeutralAndCounterposedAreDistinct

------------------------------------------------------------------------
-- 3. Coarse address alone cannot even reconstruct the prime coordinate.
------------------------------------------------------------------------

p2NotP11 : Lane.p2 ≡ Lane.p11 → ⊥
p2NotP11 ()

coarseAddressHasNoPrimeLeftInverse :
  (recoverPrime : NoGo.OggAddressCoarse10 → Lane.MonsterPrimeLane) →
  ((prime : Lane.MonsterPrimeLane) →
    recoverPrime (NoGo.addressCoarse10 prime) ≡ prime) →
  ⊥
coarseAddressHasNoPrimeLeftInverse recoverPrime leftInverse =
  p2NotP11
    (trans
      (sym (leftInverse Lane.p2))
      (trans
        (cong recoverPrime NoGo.p2AndP11HaveSameAddressCoarse10)
        (leftInverse Lane.p11)))

------------------------------------------------------------------------
-- 4. Boundary.
------------------------------------------------------------------------

record OggAddressResidualFibreBoundary : Set where
  constructor ogg-address-residual-fibre-boundary
  field
    coarseAddressIsObservationOnly : Bool
    fullPrimeInternalStateRetainedUpstairs : Bool
    residualRoundTripIsExact : Bool
    coarseAddressForgetsInternalLane : Bool
    coarseAddressCannotRecoverPrime : Bool
    residualRefinementRequiredForLosslessSemantics : Bool

open OggAddressResidualFibreBoundary public

canonicalOggAddressResidualFibreBoundary :
  OggAddressResidualFibreBoundary
canonicalOggAddressResidualFibreBoundary =
  ogg-address-residual-fibre-boundary
    true true true true true true
