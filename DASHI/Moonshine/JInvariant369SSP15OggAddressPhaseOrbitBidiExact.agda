module DASHI.Moonshine.JInvariant369SSP15OggAddressPhaseOrbitBidiExact where

------------------------------------------------------------------------
-- EXACT OGG ADDRESS <-> SSP15 LANE <-> 3 x 5 PHASE-ORBIT PRESENTATION
--
-- Branch-local capstone for PR #1053.
--
-- The authoritative identity path is:
--
--   exact Ogg address <-> Ogg/SSP15 prime lane.
--
-- Separately, a chosen finite indexing plus the structural phase-preserving
-- quotient gives:
--
--   Ogg/SSP15 prime lane
--      <-> SSP15InternalLane
--      <-> SSPTrit x NineOrbit
--      = 3 x 5.
--
-- The composed address <-> phase-orbit map is therefore an exact rechart, but
-- the phase-orbit coordinates do NOT become the canonical arithmetic identity
-- coordinates of the Ogg primes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

import DASHI.Moonshine.JInvariant369SSP15OggAddressCodecExact as Address
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as Chosen
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Reduction
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- 1. Direct exact-address <-> phase-orbit maps.
------------------------------------------------------------------------

PhaseOrbit15 : Set
PhaseOrbit15 =
  Reduction.PhaseOrbit15

addressToPhaseOrbit :
  Address.SSP15OggAddress15 ->
  PhaseOrbit15
addressToPhaseOrbit address =
  Reduction.ssp15ToPhaseOrbit
    (Chosen.primeToInternal
      (Address.ssp15LaneFromAddress address))

phaseOrbitToAddress :
  PhaseOrbit15 ->
  Address.SSP15OggAddress15
phaseOrbitToAddress state =
  Address.addressFromSSP15Lane
    (Chosen.internalToPrime
      (Reduction.phaseOrbitToSSP15 state))

------------------------------------------------------------------------
-- 2. Exact composed roundtrips.
------------------------------------------------------------------------

addressPhaseOrbitRoundTrip :
  (address : Address.SSP15OggAddress15) ->
  phaseOrbitToAddress (addressToPhaseOrbit address)
  ≡ address
addressPhaseOrbitRoundTrip address =
  trans
    (cong
      Address.addressFromSSP15Lane
      (trans
        (cong
          Chosen.internalToPrime
          (Reduction.ssp15PhaseOrbitRoundTrip
            (Chosen.primeToInternal
              (Address.ssp15LaneFromAddress address))))
        (Chosen.internalAfterPrime
          (Address.ssp15LaneFromAddress address))))
    (Address.addressAfterLane address)

phaseOrbitAddressRoundTrip :
  (state : PhaseOrbit15) ->
  addressToPhaseOrbit (phaseOrbitToAddress state)
  ≡ state
phaseOrbitAddressRoundTrip state =
  trans
    (cong
      Reduction.ssp15ToPhaseOrbit
      (trans
        (cong
          Chosen.primeToInternal
          (Address.laneAfterAddress
            (Chosen.internalToPrime
              (Reduction.phaseOrbitToSSP15 state))))
        (Chosen.primeAfterInternal
          (Reduction.phaseOrbitToSSP15 state))))
    (Reduction.phaseOrbitSSP15RoundTrip state)

------------------------------------------------------------------------
-- 3. The intermediate Ogg lane remains visible.
------------------------------------------------------------------------

addressToLane :
  Address.SSP15OggAddress15 ->
  Address.SSP15Lane
addressToLane =
  Address.ssp15LaneFromAddress

laneToAddress :
  Address.SSP15Lane ->
  Address.SSP15OggAddress15
laneToAddress =
  Address.addressFromSSP15Lane

laneToPhaseOrbit :
  Address.SSP15Lane ->
  PhaseOrbit15
laneToPhaseOrbit prime =
  Reduction.ssp15ToPhaseOrbit
    (Chosen.primeToInternal prime)

phaseOrbitToLane :
  PhaseOrbit15 ->
  Address.SSP15Lane
phaseOrbitToLane state =
  Chosen.internalToPrime
    (Reduction.phaseOrbitToSSP15 state)

lanePhaseOrbitRoundTrip :
  (prime : Address.SSP15Lane) ->
  phaseOrbitToLane (laneToPhaseOrbit prime)
  ≡ prime
lanePhaseOrbitRoundTrip prime =
  trans
    (cong
      Chosen.internalToPrime
      (Reduction.ssp15PhaseOrbitRoundTrip
        (Chosen.primeToInternal prime)))
    (Chosen.internalAfterPrime prime)

phaseOrbitLaneRoundTrip :
  (state : PhaseOrbit15) ->
  laneToPhaseOrbit (phaseOrbitToLane state)
  ≡ state
phaseOrbitLaneRoundTrip state =
  trans
    (cong
      Reduction.ssp15ToPhaseOrbit
      (Chosen.primeAfterInternal
        (Reduction.phaseOrbitToSSP15 state)))
    (Reduction.phaseOrbitSSP15RoundTrip state)

------------------------------------------------------------------------
-- 4. Exact address arithmetic survives the presentation rechart.
------------------------------------------------------------------------

phaseOrbitPrimeValue :
  PhaseOrbit15 ->
  Nat
phaseOrbitPrimeValue state =
  Lane.monsterPrimeLaneToNat
    (phaseOrbitToLane state)

phaseOrbitAddressValue :
  PhaseOrbit15 ->
  Nat
phaseOrbitAddressValue state =
  Address.addressValue
    (phaseOrbitToAddress state)

phaseOrbitAddressValueIsPrimeValue :
  (state : PhaseOrbit15) ->
  phaseOrbitAddressValue state
  ≡ phaseOrbitPrimeValue state
phaseOrbitAddressValueIsPrimeValue state =
  Address.addressValueIsSSP15Prime
    (phaseOrbitToLane state)

------------------------------------------------------------------------
-- 5. Structural source of the 3 x 5 presentation.
------------------------------------------------------------------------

phasePreservingReduction :
  DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact.Ternary27Point
  ->
  PhaseOrbit15
phasePreservingReduction =
  Reduction.reduce27ToPhaseOrbit15

canonicalPhaseOrbitLift :
  PhaseOrbit15
  ->
  DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact.Ternary27Point
canonicalPhaseOrbitLift =
  Reduction.canonicalLiftPhaseOrbit15

reduceCanonicalLiftRoundTrip :
  (state : PhaseOrbit15) ->
  phasePreservingReduction (canonicalPhaseOrbitLift state)
  ≡ state
reduceCanonicalLiftRoundTrip =
  Reduction.reduceCanonicalLift

------------------------------------------------------------------------
-- 6. Firewall.
------------------------------------------------------------------------

data AddressIdentityEqualsChosenThreeByFiveCoordinates : Set where
data ChosenIndexingBecomesCanonicalArithmeticFactorization : Set where
data FiveOrbitNamesBecomePrimeArithmeticClasses : Set where

addressIdentityNotCollapsedIntoChosenPresentation :
  AddressIdentityEqualsChosenThreeByFiveCoordinates -> ⊥
addressIdentityNotCollapsedIntoChosenPresentation ()

chosenIndexingNotPromotedToArithmeticFactorization :
  ChosenIndexingBecomesCanonicalArithmeticFactorization -> ⊥
chosenIndexingNotPromotedToArithmeticFactorization ()

fiveOrbitNamesNotPromotedToPrimeArithmeticClasses :
  FiveOrbitNamesBecomePrimeArithmeticClasses -> ⊥
fiveOrbitNamesNotPromotedToPrimeArithmeticClasses ()

record SSP15OggAddressPhaseOrbitBidiBoundary : Set where
  constructor ssp15-ogg-address-phase-orbit-bidi-boundary
  field
    exactAddressLaneBidiPaid : Bool
    chosenLaneInternalBidiPaid : Bool
    internalPhaseOrbitBidiPaid : Bool
    structuralT3ToThreeTimesFiveReductionPaid : Bool
    directAddressPhaseOrbitBidiPaid : Bool
    exactPrimeValuePreservedThroughPresentation : Bool
    authoritativeIdentityRemainsExactOggAddress : Bool
    chosenThreeByFiveIsCanonicalArithmeticFactorization : Bool
    fiveOrbitNamesArePrimeArithmeticClasses : Bool

canonicalSSP15OggAddressPhaseOrbitBidiBoundary :
  SSP15OggAddressPhaseOrbitBidiBoundary
canonicalSSP15OggAddressPhaseOrbitBidiBoundary =
  ssp15-ogg-address-phase-orbit-bidi-boundary
    true true true true true true true
    false false
