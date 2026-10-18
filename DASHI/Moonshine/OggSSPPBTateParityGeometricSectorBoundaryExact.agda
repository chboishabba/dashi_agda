module DASHI.Moonshine.OggSSPPBTateParityGeometricSectorBoundaryExact where

------------------------------------------------------------------------
-- pB TATE PARITY vs GEOMETRIC-SECTOR BOUNDARY
--
-- SOURCE MOTIVATION
--
-- Carnahan's integral modular-moonshine formulas distinguish Tate H^0 and H^1.
-- For 2B and pB classes these are the +/- trace combinations appearing in the
-- sourced formulas.
--
-- This gives a natural TWO-channel cohomological grading.
--
-- It does NOT give:
--   * the five p=2 binary-tetrahedral inertia sectors;
--   * an identification of p=3 H^0/H^1 with the Deligne--Rapoport
--     node / branch-pair orbit sectors.
--
-- At p=2 there is an immediate cardinal obstruction: 2 parity channels !=
-- 5 preferred inertia sectors.
--
-- At p=3 both carriers have two elements, so DASHI can write a finite rechart,
-- but attribution remains fail-closed: no cited source identifies Tate parity
-- with the local geometric incidence-orbit decomposition.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPSmallPrimePBIntegralTateCohomologyBridgeExact as Tate
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as P3
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Two cohomological parity channels.
------------------------------------------------------------------------

data TateParity : Set where
  evenTate : TateParity
  oddTate : TateParity

tateParityChannelCount : Nat
tateParityChannelCount = 2

p2PreferredSectorCount : Nat
p2PreferredSectorCount = 5

p3PreferredSectorCount : Nat
p3PreferredSectorCount = 2

p2ParityCountIsNotFiveSectorCount :
  tateParityChannelCount ≡ p2PreferredSectorCount -> ⊥
p2ParityCountIsNotFiveSectorCount ()

p3ParityCountMatchesTwoSectorCount :
  tateParityChannelCount ≡ p3PreferredSectorCount
p3ParityCountMatchesTwoSectorCount = refl

------------------------------------------------------------------------
-- 2. p=3 finite-shape rechart only.
------------------------------------------------------------------------

parityToP3Orbit :
  TateParity ->
  P3.P3LocalOrbit
parityToP3Orbit evenTate = P3.nodeOrbit
parityToP3Orbit oddTate = P3.branchOrbit

p3OrbitToParity :
  P3.P3LocalOrbit ->
  TateParity
p3OrbitToParity P3.nodeOrbit = evenTate
p3OrbitToParity P3.branchOrbit = oddTate

parityRoundTrip :
  (parity : TateParity) ->
  p3OrbitToParity (parityToP3Orbit parity) ≡ parity
parityRoundTrip evenTate = refl
parityRoundTrip oddTate = refl

p3OrbitRoundTrip :
  (orbit : P3.P3LocalOrbit) ->
  parityToP3Orbit (p3OrbitToParity orbit) ≡ orbit
p3OrbitRoundTrip P3.nodeOrbit = refl
p3OrbitRoundTrip P3.branchOrbit = refl

------------------------------------------------------------------------
-- 3. Attribution firewalls.
------------------------------------------------------------------------

data CarnahanTateParityIsP2FiveSectorLocalization : Set where
data CarnahanTateParityIsP3DeligneRapoportOrbitDecomposition : Set where
data EqualTwoElementCarriersCreateGeometricIdentification : Set where
data H0MeansSupersingularNodeByDefinition : Set where
data H1MeansBranchPairByDefinition : Set where

tateParityCannotBeP2FiveSectorLocalization :
  CarnahanTateParityIsP2FiveSectorLocalization -> ⊥
tateParityCannotBeP2FiveSectorLocalization ()

carnahanDoesNotIdentifyParityWithP3Geometry :
  CarnahanTateParityIsP3DeligneRapoportOrbitDecomposition -> ⊥
carnahanDoesNotIdentifyParityWithP3Geometry ()

equalTwoElementCarriersDoNotCreateIdentification :
  EqualTwoElementCarriersCreateGeometricIdentification -> ⊥
equalTwoElementCarriersDoNotCreateIdentification ()

h0NotDefinedAsSupersingularNode :
  H0MeansSupersingularNodeByDefinition -> ⊥
h0NotDefinedAsSupersingularNode ()

h1NotDefinedAsBranchPair :
  H1MeansBranchPairByDefinition -> ⊥
h1NotDefinedAsBranchPair ()

------------------------------------------------------------------------
-- 4. Existing source receipt and live boundary.
------------------------------------------------------------------------

integralTateBoundary :
  Tate.PBIntegralTateBridgeBoundary
integralTateBoundary =
  Tate.canonicalPBIntegralTateBridgeBoundary

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record PBTateParityGeometricSectorBoundary : Set where
  constructor pb-tate-parity-geometric-sector-boundary
  field
    carnahanTateParityChannelsSourced : Bool
    tateParityChannelCountTwo : Bool
    p2PreferredInertiaSectorCountFive : Bool
    p2ParityShortcutRejectedByCardinality : Bool
    p3PreferredLocalOrbitCountTwo : Bool
    p3FiniteCarrierRechartConstructed : Bool
    p3ParityGeometrySameObjectSourced : Bool
    equalCardinalityPromotedToSameObject : Bool
    attributionFirewallPreserved : Bool

canonicalPBTateParityGeometricSectorBoundary :
  PBTateParityGeometricSectorBoundary
canonicalPBTateParityGeometricSectorBoundary =
  pb-tate-parity-geometric-sector-boundary
    true true true true true true false false true
