module DASHI.Moonshine.OggSSP369RootRefinementBidiExact where

------------------------------------------------------------------------
-- OGG / SSP15 LANE <-> ROOT 369 REFINEMENT
--
-- DASHI CONTRIBUTION
--
-- The 369 refinement lane uses MonsterOntos.SSP while the Moonshine/Ogg lane
-- uses MonsterPrimeLane.  Their fifteen constructors carry the same prime
-- labels but are independent datatypes.
--
-- At depth zero the 369 address has exactly one constructor, root.  Therefore
-- a depth-zero refinement is exactly a tracked prime plus the unique root
-- address, and admits a genuine bidi with the Ogg/SSP15 lane.
--
-- The richer p-adic bridge is downstream: this file also supplies the canonical
-- root bridge section, but does not claim arbitrary bridge metadata is
-- invertible from the Ogg lane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.TrackedPrimes as TP
import DASHI.Foundations.SSPPrimeLane369Refinement as Ref
import DASHI.Physics.Closure.SSPPrimeLane369PAdicBridge as PAdic

------------------------------------------------------------------------
-- 1. Exact datatype bridge between Ogg lanes and tracked-prime lanes.
------------------------------------------------------------------------

oggToTracked :
  Lane.MonsterPrimeLane ->
  TP.SSP
oggToTracked Lane.p2 = TP.p2
oggToTracked Lane.p3 = TP.p3
oggToTracked Lane.p5 = TP.p5
oggToTracked Lane.p7 = TP.p7
oggToTracked Lane.p11 = TP.p11
oggToTracked Lane.p13 = TP.p13
oggToTracked Lane.p17 = TP.p17
oggToTracked Lane.p19 = TP.p19
oggToTracked Lane.p23 = TP.p23
oggToTracked Lane.p29 = TP.p29
oggToTracked Lane.p31 = TP.p31
oggToTracked Lane.p41 = TP.p41
oggToTracked Lane.p47 = TP.p47
oggToTracked Lane.p59 = TP.p59
oggToTracked Lane.p71 = TP.p71

trackedToOgg :
  TP.SSP ->
  Lane.MonsterPrimeLane
trackedToOgg TP.p2 = Lane.p2
trackedToOgg TP.p3 = Lane.p3
trackedToOgg TP.p5 = Lane.p5
trackedToOgg TP.p7 = Lane.p7
trackedToOgg TP.p11 = Lane.p11
trackedToOgg TP.p13 = Lane.p13
trackedToOgg TP.p17 = Lane.p17
trackedToOgg TP.p19 = Lane.p19
trackedToOgg TP.p23 = Lane.p23
trackedToOgg TP.p29 = Lane.p29
trackedToOgg TP.p31 = Lane.p31
trackedToOgg TP.p41 = Lane.p41
trackedToOgg TP.p47 = Lane.p47
trackedToOgg TP.p59 = Lane.p59
trackedToOgg TP.p71 = Lane.p71

trackedOggRoundTrip :
  (prime : Lane.MonsterPrimeLane) ->
  trackedToOgg (oggToTracked prime) ≡ prime
trackedOggRoundTrip Lane.p2 = refl
trackedOggRoundTrip Lane.p3 = refl
trackedOggRoundTrip Lane.p5 = refl
trackedOggRoundTrip Lane.p7 = refl
trackedOggRoundTrip Lane.p11 = refl
trackedOggRoundTrip Lane.p13 = refl
trackedOggRoundTrip Lane.p17 = refl
trackedOggRoundTrip Lane.p19 = refl
trackedOggRoundTrip Lane.p23 = refl
trackedOggRoundTrip Lane.p29 = refl
trackedOggRoundTrip Lane.p31 = refl
trackedOggRoundTrip Lane.p41 = refl
trackedOggRoundTrip Lane.p47 = refl
trackedOggRoundTrip Lane.p59 = refl
trackedOggRoundTrip Lane.p71 = refl

oggTrackedRoundTrip :
  (prime : TP.SSP) ->
  oggToTracked (trackedToOgg prime) ≡ prime
oggTrackedRoundTrip TP.p2 = refl
oggTrackedRoundTrip TP.p3 = refl
oggTrackedRoundTrip TP.p5 = refl
oggTrackedRoundTrip TP.p7 = refl
oggTrackedRoundTrip TP.p11 = refl
oggTrackedRoundTrip TP.p13 = refl
oggTrackedRoundTrip TP.p17 = refl
oggTrackedRoundTrip TP.p19 = refl
oggTrackedRoundTrip TP.p23 = refl
oggTrackedRoundTrip TP.p29 = refl
oggTrackedRoundTrip TP.p31 = refl
oggTrackedRoundTrip TP.p41 = refl
oggTrackedRoundTrip TP.p47 = refl
oggTrackedRoundTrip TP.p59 = refl
oggTrackedRoundTrip TP.p71 = refl

------------------------------------------------------------------------
-- 2. Exact Ogg lane <-> depth-zero 369 refinement.
------------------------------------------------------------------------

Root369Refinement : Set
Root369Refinement =
  Ref.SSPPrimeLane369Refinement zero

oggToRoot369 :
  Lane.MonsterPrimeLane ->
  Root369Refinement
oggToRoot369 prime =
  Ref.mkSSPPrimeLane369Refinement
    (oggToTracked prime)
    Ref.root

root369ToOgg :
  Root369Refinement ->
  Lane.MonsterPrimeLane
root369ToOgg refinement =
  trackedToOgg (Ref.primeLane refinement)

root369OggRoundTrip :
  (prime : Lane.MonsterPrimeLane) ->
  root369ToOgg (oggToRoot369 prime) ≡ prime
root369OggRoundTrip prime =
  trackedOggRoundTrip prime

oggRoot369RoundTrip :
  (refinement : Root369Refinement) ->
  oggToRoot369 (root369ToOgg refinement) ≡ refinement
oggRoot369RoundTrip
  (Ref.mkSSPPrimeLane369Refinement prime Ref.root)
  rewrite oggTrackedRoundTrip prime = refl

------------------------------------------------------------------------
-- 3. Canonical root p-adic bridge section.
------------------------------------------------------------------------

oggToCanonicalRootPAdicBridge :
  Lane.MonsterPrimeLane ->
  PAdic.SSPPrimeLane369PAdicBridge
oggToCanonicalRootPAdicBridge Lane.p2 = PAdic.canonicalRootBridgeP2
oggToCanonicalRootPAdicBridge Lane.p3 = PAdic.canonicalRootBridgeP3
oggToCanonicalRootPAdicBridge Lane.p5 = PAdic.canonicalRootBridgeP5
oggToCanonicalRootPAdicBridge Lane.p7 = PAdic.canonicalRootBridgeP7
oggToCanonicalRootPAdicBridge Lane.p11 = PAdic.canonicalRootBridgeP11
oggToCanonicalRootPAdicBridge Lane.p13 = PAdic.canonicalRootBridgeP13
oggToCanonicalRootPAdicBridge Lane.p17 = PAdic.canonicalRootBridgeP17
oggToCanonicalRootPAdicBridge Lane.p19 = PAdic.canonicalRootBridgeP19
oggToCanonicalRootPAdicBridge Lane.p23 = PAdic.canonicalRootBridgeP23
oggToCanonicalRootPAdicBridge Lane.p29 = PAdic.canonicalRootBridgeP29
oggToCanonicalRootPAdicBridge Lane.p31 = PAdic.canonicalRootBridgeP31
oggToCanonicalRootPAdicBridge Lane.p41 = PAdic.canonicalRootBridgeP41
oggToCanonicalRootPAdicBridge Lane.p47 = PAdic.canonicalRootBridgeP47
oggToCanonicalRootPAdicBridge Lane.p59 = PAdic.canonicalRootBridgeP59
oggToCanonicalRootPAdicBridge Lane.p71 = PAdic.canonicalRootBridgeP71

pAdicBridgeToOggLane :
  PAdic.SSPPrimeLane369PAdicBridge ->
  Lane.MonsterPrimeLane
pAdicBridgeToOggLane bridge =
  trackedToOgg
    (Ref.primeLane (PAdic.depthRefinement bridge))

canonicalRootPAdicSectionRoundTrip :
  (prime : Lane.MonsterPrimeLane) ->
  pAdicBridgeToOggLane
    (oggToCanonicalRootPAdicBridge prime)
  ≡ prime
canonicalRootPAdicSectionRoundTrip Lane.p2 = refl
canonicalRootPAdicSectionRoundTrip Lane.p3 = refl
canonicalRootPAdicSectionRoundTrip Lane.p5 = refl
canonicalRootPAdicSectionRoundTrip Lane.p7 = refl
canonicalRootPAdicSectionRoundTrip Lane.p11 = refl
canonicalRootPAdicSectionRoundTrip Lane.p13 = refl
canonicalRootPAdicSectionRoundTrip Lane.p17 = refl
canonicalRootPAdicSectionRoundTrip Lane.p19 = refl
canonicalRootPAdicSectionRoundTrip Lane.p23 = refl
canonicalRootPAdicSectionRoundTrip Lane.p29 = refl
canonicalRootPAdicSectionRoundTrip Lane.p31 = refl
canonicalRootPAdicSectionRoundTrip Lane.p41 = refl
canonicalRootPAdicSectionRoundTrip Lane.p47 = refl
canonicalRootPAdicSectionRoundTrip Lane.p59 = refl
canonicalRootPAdicSectionRoundTrip Lane.p71 = refl

------------------------------------------------------------------------
-- 4. Firewall.
------------------------------------------------------------------------

data Root369RefinementIsAnalyticPAdicField : Set where
data CanonicalRootBridgeSectionIsFullBridgeBijection : Set where
data MatchingPrimeLabelsCreatesSemanticIdentityWithoutBridge : Set where

root369DoesNotConstructAnalyticPAdicField :
  Root369RefinementIsAnalyticPAdicField -> ⊥
root369DoesNotConstructAnalyticPAdicField ()

rootBridgeSectionNotPromotedToFullBridgeBijection :
  CanonicalRootBridgeSectionIsFullBridgeBijection -> ⊥
rootBridgeSectionNotPromotedToFullBridgeBijection ()

primeLabelsNotSilentlyIdentified :
  MatchingPrimeLabelsCreatesSemanticIdentityWithoutBridge -> ⊥
primeLabelsNotSilentlyIdentified ()

record OggSSP369RootRefinementBidiBoundary : Set where
  constructor ogg-ssp369-root-refinement-bidi-boundary
  field
    oggTrackedPrimeDatatypeBidiPaid : Bool
    oggRoot369RefinementBidiPaid : Bool
    rootAddressUniquenessUsed : Bool
    canonicalRootPAdicSectionOwned : Bool
    canonicalRootSectionRecoversOggLane : Bool
    analyticPAdicFieldConstructed : Bool
    arbitraryPAdicBridgeBijectionClaimed : Bool

canonicalOggSSP369RootRefinementBidiBoundary :
  OggSSP369RootRefinementBidiBoundary
canonicalOggSSP369RootRefinementBidiBoundary =
  ogg-ssp369-root-refinement-bidi-boundary
    true true true true true
    false false
