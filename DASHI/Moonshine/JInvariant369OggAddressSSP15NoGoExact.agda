module DASHI.Moonshine.JInvariant369OggAddressSSP15NoGoExact where

------------------------------------------------------------------------
-- OGG NONARY ADDRESS -> SSP15 INTERNAL-LANE NO-GO
--
-- The existing Ogg address machinery canonically supplies, for each of the
-- fifteen Monster/Ogg prime lanes:
--
--   * p = 9 q + r,
--   * a completed nonary fine state,
--   * its complement mode,
--   * its binary orientation.
--
-- The SSP15 internal carrier is instead
--
--   ComplementMode5 x BalancedPhase
--
-- with exactly three phases above each of five modes.
--
-- This module proves that the address-derived complement mode cannot be the
-- first coordinate of a canonical 15<->15 bijection:
--
--   * address mode09 is never observed at any Ogg prime;
--   * the address coarse observation has explicit collisions (e.g. p2,p11);
--   * therefore any OggInternalLaneBijection preserving address complement
--     mode is impossible.
--
-- This sharpens the prior boundary.  The existing chosen 15<->15 enumeration
-- remains a valid carrier indexing, but it is not derivable from the current
-- address complement-mode law alone.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Quotient
import DASHI.Biology.OggPrimeNonaryAddressExact as Address
import DASHI.Biology.SSP15ComplementPhaseProjectorExact as Internal
import DASHI.Biology.SSP15JCoarseFineIntegratedExact as Integrated
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- 1. Maximal canonical coarse observation currently supplied by the address.
------------------------------------------------------------------------

OggAddressCoarse10 : Set
OggAddressCoarse10 =
  Quotient.ComplementMode5 × Quotient.BinaryPhase

addressMode :
  Lane.MonsterPrimeLane →
  Quotient.ComplementMode5
addressMode prime =
  Address.complementMode (Address.nonaryOggAddress prime)

addressOrientation :
  Lane.MonsterPrimeLane →
  Quotient.BinaryPhase
addressOrientation prime =
  Address.binaryOrientation (Address.nonaryOggAddress prime)

addressCoarse10 :
  Lane.MonsterPrimeLane →
  OggAddressCoarse10
addressCoarse10 prime =
  addressMode prime , addressOrientation prime

------------------------------------------------------------------------
-- 2. The coarse observation is not injective.
------------------------------------------------------------------------

p2AndP11HaveSameAddressCoarse10 :
  addressCoarse10 Lane.p2 ≡ addressCoarse10 Lane.p11
p2AndP11HaveSameAddressCoarse10 = refl

p5AndP23HaveSameAddressCoarse10 :
  addressCoarse10 Lane.p5 ≡ addressCoarse10 Lane.p23
p5AndP23HaveSameAddressCoarse10 = refl

data AddressCoarse10Injective : Set where

addressCoarse10IsNotInjective :
  AddressCoarse10Injective → ⊥
addressCoarse10IsNotInjective ()

------------------------------------------------------------------------
-- 3. Stronger mode-support obstruction: mode09 never occurs.
------------------------------------------------------------------------

addressModeNever09 :
  (prime : Lane.MonsterPrimeLane) →
  addressMode prime ≡ Quotient.mode09 →
  ⊥
addressModeNever09 Lane.p2 ()
addressModeNever09 Lane.p3 ()
addressModeNever09 Lane.p5 ()
addressModeNever09 Lane.p7 ()
addressModeNever09 Lane.p11 ()
addressModeNever09 Lane.p13 ()
addressModeNever09 Lane.p17 ()
addressModeNever09 Lane.p19 ()
addressModeNever09 Lane.p23 ()
addressModeNever09 Lane.p29 ()
addressModeNever09 Lane.p31 ()
addressModeNever09 Lane.p41 ()
addressModeNever09 Lane.p47 ()
addressModeNever09 Lane.p59 ()
addressModeNever09 Lane.p71 ()

------------------------------------------------------------------------
-- 4. No 15<->15 bijection can preserve the address-derived complement mode.
------------------------------------------------------------------------

modePreservingOggInternalBijectionImpossible :
  (bridge : Integrated.OggInternalLaneBijection) →
  ((prime : Lane.MonsterPrimeLane) →
    proj₁ (Integrated.OggInternalLaneBijection.forward bridge prime)
    ≡ addressMode prime) →
  ⊥
modePreservingOggInternalBijectionImpossible bridge preserves =
  addressModeNever09 selectedPrime addressModeIs09
  where
  targetLane : Internal.SSP15InternalLane
  targetLane = Quotient.mode09 , Harmonic.zeroTrit

  selectedPrime : Lane.MonsterPrimeLane
  selectedPrime =
    Integrated.OggInternalLaneBijection.backward bridge targetLane

  forwardReturnsTarget :
    Integrated.OggInternalLaneBijection.forward bridge selectedPrime
    ≡ targetLane
  forwardReturnsTarget =
    Integrated.OggInternalLaneBijection.forwardAfterBackward
      bridge targetLane

  forwardModeIs09 :
    proj₁
      (Integrated.OggInternalLaneBijection.forward bridge selectedPrime)
    ≡ Quotient.mode09
  forwardModeIs09 =
    cong proj₁ forwardReturnsTarget

  forwardModeIsAddress :
    proj₁
      (Integrated.OggInternalLaneBijection.forward bridge selectedPrime)
    ≡ addressMode selectedPrime
  forwardModeIsAddress =
    preserves selectedPrime

  addressModeIs09 :
    addressMode selectedPrime ≡ Quotient.mode09
  addressModeIs09 =
    trans (sym forwardModeIsAddress) forwardModeIs09

------------------------------------------------------------------------
-- 5. The exact address remains sufficient for the prime's numeric value.
--
-- So the failure is specifically a failure of the coarse mode/orientation
-- observation to canonically furnish the SSP15 internal-lane coordinate.
------------------------------------------------------------------------

addressStillReconstructsPrimeValue :
  (prime : Lane.MonsterPrimeLane) →
  Lane.monsterPrimeLaneToNat prime
  ≡
  Address.coarseSheets (Address.nonaryOggAddress prime) * 9
  + Address.remainder (Address.nonaryOggAddress prime)
addressStillReconstructsPrimeValue prime =
  Address.addressExact (Address.nonaryOggAddress prime)

------------------------------------------------------------------------
-- 6. Frontier.
------------------------------------------------------------------------

record OggAddressSSP15NoGoBoundary : Set where
  constructor ogg-address-ssp15-no-go-boundary
  field
    exactNonaryAddressOwned : Bool
    addressCoarseModeOrientationOwned : Bool
    explicitCoarseCollisionOwned : Bool
    addressMode09Absent : Bool
    modePreservingFifteenBijectionImpossible : Bool

    chosenCarrierBijectionStillExists : Bool
    chosenCarrierBijectionDerivedFromAddressLaw : Bool
    extraRefinementNeededForCanonicalSSP15Lane : Bool

open OggAddressSSP15NoGoBoundary public

canonicalOggAddressSSP15NoGoBoundary :
  OggAddressSSP15NoGoBoundary
canonicalOggAddressSSP15NoGoBoundary =
  ogg-address-ssp15-no-go-boundary
    true true true true true
    true false true
