module DASHI.Moonshine.OggSSPClimbingGymExactHoleRadixCodec where

------------------------------------------------------------------------
-- EXACT FINITE HOLE-VERTEX -> RADIX ADDRESS
--
-- For a JMD wall form p^a the analytic hole ladder is
--
--     h_m = 2*pi*m / (p^a log p).
--
-- Its declared phase vertex is the rational point m / p^a modulo one.  That
-- finite vertex does not require a constructive-real floor operation: its
-- address is exactly the lowest a base-p digits of the natural index m.
--
-- This module therefore compiles m directly into the already-owned native-p
-- RadialTreeAddress through `NatRadialTreeCodecExact`.  The analytic theorem
-- identifying the real phase of h_m with m/p^a remains a separate obligation;
-- once that equality is supplied, no second real quantisation is needed on the
-- hole side.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.NatRadialTreeCodecExact as NatRadix
import DASHI.Foundations.RadixValuationStageBridge as Radix
import DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact as Gym

ExactHoleRadixAddress : Gym.WallForm → Set
ExactHoleRadixAddress form =
  Radix.RadialTreeAddress
    (Gym.oggPrimeRadixChart (Gym.formLane form))
    (Gym.formExponent form)

exactHoleRadialAddress :
  (form : Gym.WallForm) →
  Nat →
  ExactHoleRadixAddress form
exactHoleRadialAddress form m =
  NatRadix.natRadialAddress
    (Gym.oggPrimeRadixChart (Gym.formLane form))
    (Gym.formExponent form)
    m

exactHoleRadialValue :
  (form : Gym.WallForm) →
  Nat →
  Nat
exactHoleRadialValue form m =
  NatRadix.radialValue
    (Gym.oggPrimeRadixChart (Gym.formLane form))
    (exactHoleRadialAddress form m)

------------------------------------------------------------------------
-- Exact concrete fixtures from the supplied wall forms.
------------------------------------------------------------------------

p2Depth1M3Value : exactHoleRadialValue Gym.p2Exponent1 3 ≡ 1
p2Depth1M3Value = refl

p2Depth3M13Value : exactHoleRadialValue Gym.p2Exponent3 13 ≡ 5
p2Depth3M13Value = refl

p3Depth2M14Value : exactHoleRadialValue Gym.p3Exponent2 14 ≡ 5
p3Depth2M14Value = refl

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record ExactHoleRadixCodecBoundary : Set where
  constructor exact-hole-radix-codec-boundary
  field
    exactNaturalIndexCompilerConstructed : Bool
    existingNativePrimeRadixTreeReused : Bool
    holeVertexAddressIsFiniteArithmetic : Bool
    holeAddressNeedsConstructiveRealFloor : Bool

    analyticHolePhaseIdentityConstructedHere : Bool
    arbitraryRealPhaseQuantiserConstructedHere : Bool
    finiteHoleAddressProvesZetaParametrisation : Bool

open ExactHoleRadixCodecBoundary public

canonicalExactHoleRadixCodecBoundary : ExactHoleRadixCodecBoundary
canonicalExactHoleRadixCodecBoundary =
  exact-hole-radix-codec-boundary
    true true true false
    false false false
