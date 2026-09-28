module DASHI.Moonshine.OggSSP369CanonicalThreeSixNineLiftExact where

------------------------------------------------------------------------
-- OGG / SSP15 -> CANONICAL [3,6,9] DEPTH-3 LANE SLICE
--
-- DASHI CONTRIBUTION
--
-- A full depth-three 369 refinement has many addresses, so it is NOT
-- bidirectional with the fifteen Ogg lanes.
--
-- The canonical [3,6,9] slice fixes the address and leaves only the tracked
-- prime lane free.  That slice is therefore exactly bidirectional with the
-- Ogg/SSP15 lane carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.TrackedPrimes as TP
import DASHI.Foundations.SSPPrimeLane369Refinement as Ref
import DASHI.Moonshine.OggSSP369RootRefinementBidiExact as Root

depthThree : Nat
depthThree = suc (suc (suc zero))

record CanonicalThreeSixNineLane : Set where
  constructor canonical-three-six-nine-lane
  field
    trackedPrime : TP.SSP

open CanonicalThreeSixNineLane public

canonicalRefinement :
  CanonicalThreeSixNineLane ->
  Ref.SSPPrimeLane369Refinement depthThree
canonicalRefinement lane =
  Ref.mkSSPPrimeLane369Refinement
    (trackedPrime lane)
    Ref.canonicalThreeSixNineAddress

canonicalRefinementPrimeExact :
  (lane : CanonicalThreeSixNineLane) ->
  Ref.primeLane (canonicalRefinement lane)
  ≡ trackedPrime lane
canonicalRefinementPrimeExact lane = refl

canonicalRefinementAddressExact :
  (lane : CanonicalThreeSixNineLane) ->
  Ref.address (canonicalRefinement lane)
  ≡ Ref.canonicalThreeSixNineAddress
canonicalRefinementAddressExact lane = refl

canonicalRefinementDigitsExact :
  (lane : CanonicalThreeSixNineLane) ->
  Ref.addressDigits (Ref.address (canonicalRefinement lane))
  ≡ Ref.digit-3 ∷ Ref.digit-6 ∷ Ref.digit-9 ∷ []
canonicalRefinementDigitsExact lane =
  Ref.canonicalThreeSixNineDigits

------------------------------------------------------------------------
-- 1. Exact Ogg <-> canonical [3,6,9] slice.
------------------------------------------------------------------------

oggToCanonical369 :
  Lane.MonsterPrimeLane ->
  CanonicalThreeSixNineLane
oggToCanonical369 prime =
  canonical-three-six-nine-lane
    (Root.oggToTracked prime)

canonical369ToOgg :
  CanonicalThreeSixNineLane ->
  Lane.MonsterPrimeLane
canonical369ToOgg lane =
  Root.trackedToOgg (trackedPrime lane)

canonical369OggRoundTrip :
  (prime : Lane.MonsterPrimeLane) ->
  canonical369ToOgg (oggToCanonical369 prime)
  ≡ prime
canonical369OggRoundTrip =
  Root.trackedOggRoundTrip

oggCanonical369RoundTrip :
  (lane : CanonicalThreeSixNineLane) ->
  oggToCanonical369 (canonical369ToOgg lane)
  ≡ lane
oggCanonical369RoundTrip
  (canonical-three-six-nine-lane prime)
  rewrite Root.oggTrackedRoundTrip prime = refl

------------------------------------------------------------------------
-- 2. Root -> canonical [3,6,9] lift preserves the lane exactly.
------------------------------------------------------------------------

rootToCanonical369 :
  Root.Root369Refinement ->
  CanonicalThreeSixNineLane
rootToCanonical369 root =
  canonical-three-six-nine-lane
    (Ref.primeLane root)

canonical369ToRoot :
  CanonicalThreeSixNineLane ->
  Root.Root369Refinement
canonical369ToRoot lane =
  Ref.mkSSPPrimeLane369Refinement
    (trackedPrime lane)
    Ref.root

rootCanonical369RoundTrip :
  (root : Root.Root369Refinement) ->
  canonical369ToRoot (rootToCanonical369 root)
  ≡ root
rootCanonical369RoundTrip
  (Ref.mkSSPPrimeLane369Refinement prime Ref.root) = refl

canonical369RootRoundTrip :
  (lane : CanonicalThreeSixNineLane) ->
  rootToCanonical369 (canonical369ToRoot lane)
  ≡ lane
canonical369RootRoundTrip
  (canonical-three-six-nine-lane prime) = refl

rootLiftPrimePreserved :
  (root : Root.Root369Refinement) ->
  Ref.primeLane
    (canonicalRefinement (rootToCanonical369 root))
  ≡ Ref.primeLane root
rootLiftPrimePreserved root = refl

------------------------------------------------------------------------
-- 3. Firewall.
------------------------------------------------------------------------

data CanonicalSliceEqualsFullDepthThreeTree : Set where
data ThreeByFivePresentationGeneratesThreeSixNineDigits : Set where
data Canonical369LiftCreatesPAdicAnalysis : Set where

canonicalSliceNotPromotedToFullDepthThreeTree :
  CanonicalSliceEqualsFullDepthThreeTree -> ⊥
canonicalSliceNotPromotedToFullDepthThreeTree ()

threeByFiveDoesNotGenerateCanonicalDigits :
  ThreeByFivePresentationGeneratesThreeSixNineDigits -> ⊥
threeByFiveDoesNotGenerateCanonicalDigits ()

canonicalLiftDoesNotCreatePAdicAnalysis :
  Canonical369LiftCreatesPAdicAnalysis -> ⊥
canonicalLiftDoesNotCreatePAdicAnalysis ()

record OggSSP369CanonicalThreeSixNineLiftBoundary : Set where
  constructor ogg-ssp369-canonical-three-six-nine-lift-boundary
  field
    canonicalDepthThreeAddressFixed : Bool
    canonicalDigitsThreeSixNineExact : Bool
    oggCanonicalSliceBidiPaid : Bool
    rootCanonicalSliceBidiPaid : Bool
    lanePreservedUnderCanonicalLift : Bool
    canonicalSliceEqualsFullDepthThreeTree : Bool
    threeByFiveGeneratesThreeSixNineDigits : Bool
    analyticPAdicStructureConstructed : Bool

canonicalOggSSP369CanonicalThreeSixNineLiftBoundary :
  OggSSP369CanonicalThreeSixNineLiftBoundary
canonicalOggSSP369CanonicalThreeSixNineLiftBoundary =
  ogg-ssp369-canonical-three-six-nine-lift-boundary
    true true true true true
    false false false
