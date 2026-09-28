module DASHI.Moonshine.OggSSP15PhaseOrbitBidiExact where

------------------------------------------------------------------------
-- OGG / SSP15 <-> 3 x 5 PHASE-ORBIT PRESENTATION
--
-- DASHI CONTRIBUTION
--
-- Compose two existing theorem-bearing bridges:
--
--   1. CHOSEN finite indexing:
--        MonsterPrimeLane <-> SSP15InternalLane
--
--   2. STRUCTURAL finite quotient presentation:
--        SSP15InternalLane <-> SSPTrit x NineOrbit
--                            = 3 x 5.
--
-- This yields a literal two-sided carrier rechart
--
--        MonsterPrimeLane <-> PhaseOrbit15.
--
-- Authority boundary:
-- * MonsterPrimeLane is the authoritative SSP15/Ogg carrier.
-- * exact Ogg (q,r) address remains the canonical lane identity mechanism.
-- * the Ogg <-> internal-lane leg is a chosen ordinal/indexing equivalence.
-- * the internal-lane <-> 3x5 phase-orbit leg is structurally induced by the
--   phase-preserving quotient T^3 -> T x (T^2 / inner inversion).
-- * no claim is made that the chosen 3x5 coordinates are arithmetic invariants
--   of Ogg primes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Biology.SSP15ComplementPhaseProjectorExact as Internal
import DASHI.Biology.OggPrimeNonaryAddressExact as Address
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as Chosen
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Reduction

------------------------------------------------------------------------
-- 1. Presentation carrier.
------------------------------------------------------------------------

OggSSP15Lane : Set
OggSSP15Lane =
  Lane.MonsterPrimeLane

PhaseOrbit15 : Set
PhaseOrbit15 =
  Reduction.PhaseOrbit15

------------------------------------------------------------------------
-- 2. Compose the two existing directions.
------------------------------------------------------------------------

oggToPhaseOrbit15 :
  OggSSP15Lane ->
  PhaseOrbit15
oggToPhaseOrbit15 prime =
  Reduction.ssp15ToPhaseOrbit
    (Chosen.primeToInternal prime)

phaseOrbit15ToOgg :
  PhaseOrbit15 ->
  OggSSP15Lane
phaseOrbit15ToOgg state =
  Chosen.internalToPrime
    (Reduction.phaseOrbitToSSP15 state)

------------------------------------------------------------------------
-- 3. Exact bidi roundtrips.
------------------------------------------------------------------------

oggAfterPhaseOrbit :
  (prime : OggSSP15Lane) ->
  phaseOrbit15ToOgg (oggToPhaseOrbit15 prime)
  ≡ prime
oggAfterPhaseOrbit prime =
  trans
    (cong
      Chosen.internalToPrime
      (Reduction.ssp15PhaseOrbitRoundTrip
        (Chosen.primeToInternal prime)))
    (Chosen.internalAfterPrime prime)

phaseOrbitAfterOgg :
  (state : PhaseOrbit15) ->
  oggToPhaseOrbit15 (phaseOrbit15ToOgg state)
  ≡ state
phaseOrbitAfterOgg state =
  trans
    (cong
      Reduction.ssp15ToPhaseOrbit
      (Chosen.primeAfterInternal
        (Reduction.phaseOrbitToSSP15 state)))
    (Reduction.phaseOrbitSSP15RoundTrip state)

------------------------------------------------------------------------
-- 4. Intermediate lane rechart is visible and separately typed.
------------------------------------------------------------------------

oggToInternal :
  OggSSP15Lane ->
  Internal.SSP15InternalLane
oggToInternal =
  Chosen.primeToInternal

internalToOgg :
  Internal.SSP15InternalLane ->
  OggSSP15Lane
internalToOgg =
  Chosen.internalToPrime

internalToPhaseOrbit :
  Internal.SSP15InternalLane ->
  PhaseOrbit15
internalToPhaseOrbit =
  Reduction.ssp15ToPhaseOrbit

phaseOrbitToInternal :
  PhaseOrbit15 ->
  Internal.SSP15InternalLane
phaseOrbitToInternal =
  Reduction.phaseOrbitToSSP15

------------------------------------------------------------------------
-- 5. Exact 3 x 5 arithmetic is inherited from the structural quotient.
------------------------------------------------------------------------

phaseCount : Nat
phaseCount =
  Reduction.outerPhaseCount

fiveOrbitCount : Nat
fiveOrbitCount =
  Reduction.innerOrbitCount

presentationCount : Nat
presentationCount =
  Reduction.phaseOrbitStateCount

phaseCountIsThree :
  phaseCount ≡ 3
phaseCountIsThree = refl

fiveOrbitCountIsFive :
  fiveOrbitCount ≡ 5
fiveOrbitCountIsFive = refl

presentationCountIsFifteen :
  presentationCount ≡ 15
presentationCountIsFifteen =
  Reduction.phaseOrbitStateCountIsFifteen

------------------------------------------------------------------------
-- 6. Canonical Ogg address stays authoritative and independent.
------------------------------------------------------------------------

oggAddress :
  (prime : OggSSP15Lane) ->
  Address.NonaryOggAddress prime
oggAddress =
  Address.nonaryOggAddress

oggAddressReconstructsPrimeValue :
  (prime : OggSSP15Lane) ->
  Lane.monsterPrimeLaneToNat prime
  ≡ Address.coarseSheets (oggAddress prime) * 9
    + Address.remainder (oggAddress prime)
oggAddressReconstructsPrimeValue prime =
  Address.addressExact (oggAddress prime)

data ChosenPhaseOrbitPresentationIsCanonicalOggAddress : Set where
data FiveOrbitCoordinateIsArithmeticPrimeInvariant : Set where
data ThreeByFivePresentationRedefinesSSP15Carrier : Set where

phaseOrbitPresentationDoesNotReplaceCanonicalAddress :
  ChosenPhaseOrbitPresentationIsCanonicalOggAddress -> ⊥
phaseOrbitPresentationDoesNotReplaceCanonicalAddress ()

fiveOrbitCoordinateNotPromotedToArithmeticInvariant :
  FiveOrbitCoordinateIsArithmeticPrimeInvariant -> ⊥
fiveOrbitCoordinateNotPromotedToArithmeticInvariant ()

threeByFiveDoesNotRedefineSSP15 :
  ThreeByFivePresentationRedefinesSSP15Carrier -> ⊥
threeByFiveDoesNotRedefineSSP15 ()

------------------------------------------------------------------------
-- 7. Machine-readable authority boundary.
------------------------------------------------------------------------

record OggSSP15PhaseOrbitBidiBoundary : Set where
  constructor ogg-ssp15-phase-orbit-bidi-boundary
  field
    authoritativeCarrierIsOggPrimeLane : Bool
    exactOggAddressRemainsCanonicalIdentity : Bool
    chosenOggInternalIndexingReused : Bool
    internalToThreeByFiveStructuralBidiReused : Bool
    composedOggToThreeByFiveForward : Bool
    composedThreeByFiveToOggBackward : Bool
    composedRoundTripsPaid : Bool
    threeTimesFiveIsFifteen : Bool
    chosenPresentationIsCanonicalAddress : Bool
    fiveOrbitIsArithmeticPrimeInvariant : Bool
    presentationRedefinesSSP15Carrier : Bool

canonicalOggSSP15PhaseOrbitBidiBoundary :
  OggSSP15PhaseOrbitBidiBoundary
canonicalOggSSP15PhaseOrbitBidiBoundary =
  ogg-ssp15-phase-orbit-bidi-boundary
    true true true true true true true true
    false false false
