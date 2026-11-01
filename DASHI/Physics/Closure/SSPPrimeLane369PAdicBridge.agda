module DASHI.Physics.Closure.SSPPrimeLane369PAdicBridge where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.FifteenSSP369Forest as Forest
import DASHI.Foundations.SSPPrimeLane369Refinement as Ref
import DASHI.Physics.Closure.MultiPrimePAdicCarrierCoordinate as Carrier
import DASHI.TrackedPrimes as TP
import Ontology.GodelLattice as GL

------------------------------------------------------------------------
-- Typed bridge from a depth-refined 369 lane carrier into the finite p-adic
-- coordinate tuple story.
--
-- The bridge stays strictly finite and explicit:
--   * it records the depth address and refinement witness,
--   * it packages the corresponding p-adic coordinate witness,
--   * it keeps the coordinate tuple ordinal separate from the refinement depth,
--   * it exposes canonical root and 3/6/9 examples,
--   * it also packages a 15-lane root forest over the tracked prime order.

three : Nat
three = suc (suc (suc zero))

formalPAdicCoordinateRole : String
formalPAdicCoordinateRole =
  "formal p-adic prime-lane coordinate in the Vec15 adelic carrier tuple"

formalPAdicResiduePlaceholder : String
formalPAdicResiduePlaceholder =
  "residue data intentionally not supplied by this carrier receipt"

record SSPPrimeLane369PAdicBridge : Set where
  constructor mkSSPPrimeLane369PAdicBridge
  field
    depth :
      Nat

    depthAddress :
      Ref.Lane369Address depth

    depthRefinement :
      Ref.SSPPrimeLane369Refinement depth

    tupleOrdinal :
      Nat

    coordinateLabel :
      String

    coordinate :
      Carrier.PAdicCarrierCoordinate

    depthAddressMatches :
      Ref.address depthRefinement ≡ depthAddress

    coordinatePrimeMatches :
      Carrier.coordinatePrime coordinate ≡ Ref.primeLane depthRefinement

    coordinateOrdinalMatches :
      Carrier.coordinateOrdinal coordinate ≡ tupleOrdinal

    coordinateLabelMatches :
      Carrier.coordinateLabel coordinate ≡ coordinateLabel

    coordinateStatusMatches :
      Carrier.coordinateStatus coordinate ≡ Carrier.canonicalPAdicCoordinateStatus

    coordinateRoleMatches :
      Carrier.coordinateRole coordinate ≡ formalPAdicCoordinateRole

    coordinateResiduePlaceholderMatches :
      Carrier.residuePlaceholder coordinate ≡ formalPAdicResiduePlaceholder

    analyticPAdicFieldConstructedIsFalse :
      Carrier.analyticPAdicFieldConstructed coordinate ≡ false

    pAdicNormConstructedIsFalse :
      Carrier.pAdicNormConstructed coordinate ≡ false

open SSPPrimeLane369PAdicBridge public

mkBridge :
  ∀ {d : Nat} →
  Ref.SSPPrimeLane369Refinement d →
  Ref.Lane369Address d →
  Nat →
  String →
  SSPPrimeLane369PAdicBridge
mkBridge {d} refinement address ordinal label =
  record
    { depth =
        d
    ; depthAddress =
        Ref.address refinement
    ; depthRefinement =
        refinement
    ; tupleOrdinal =
        ordinal
    ; coordinateLabel =
        label
    ; coordinate =
        Carrier.mkFormalPAdicCoordinate
          (Ref.primeLane refinement)
          ordinal
          label
    ; depthAddressMatches =
        refl
    ; coordinatePrimeMatches =
        refl
    ; coordinateOrdinalMatches =
        refl
    ; coordinateLabelMatches =
        refl
    ; coordinateStatusMatches =
        refl
    ; coordinateRoleMatches =
        refl
    ; coordinateResiduePlaceholderMatches =
        refl
    ; analyticPAdicFieldConstructedIsFalse =
        refl
    ; pAdicNormConstructedIsFalse =
        refl
    }

mkRootBridge :
  Ref.SSPPrimeLane369Refinement zero →
  Nat →
  String →
  SSPPrimeLane369PAdicBridge
mkRootBridge refinement ordinal label =
  mkBridge refinement Ref.root ordinal label

mkThreeSixNineBridge :
  Ref.SSPPrimeLane369Refinement three →
  Nat →
  String →
  SSPPrimeLane369PAdicBridge
mkThreeSixNineBridge refinement ordinal label =
  mkBridge refinement Ref.canonicalThreeSixNineAddress ordinal label

canonicalRootP3Bridge :
  SSPPrimeLane369PAdicBridge
canonicalRootP3Bridge =
  mkRootBridge Ref.canonicalRootLane369Refinement 1 "p3"

canonicalThreeSixNineP3Bridge :
  SSPPrimeLane369PAdicBridge
canonicalThreeSixNineP3Bridge =
  mkThreeSixNineBridge Ref.canonicalThreeSixNineLane369Refinement 1 "p3"

canonicalThreeSixNineP7Bridge :
  SSPPrimeLane369PAdicBridge
canonicalThreeSixNineP7Bridge =
  mkThreeSixNineBridge
    (Ref.mkSSPPrimeLane369Refinement TP.p7 Ref.canonicalThreeSixNineAddress)
    3
    "p7"

canonicalRootBridgeP2 :
  SSPPrimeLane369PAdicBridge
canonicalRootBridgeP2 = mkRootBridge (Ref.mkSSPPrimeLane369Refinement TP.p2 Ref.root) 0 "p2"

canonicalRootBridgeP3 :
  SSPPrimeLane369PAdicBridge
canonicalRootBridgeP3 = mkRootBridge Ref.canonicalRootLane369Refinement 1 "p3"

canonicalRootBridgeP5 :
  SSPPrimeLane369PAdicBridge
canonicalRootBridgeP5 = mkRootBridge (Ref.mkSSPPrimeLane369Refinement TP.p5 Ref.root) 2 "p5"

canonicalRootBridgeP7 :
  SSPPrimeLane369PAdicBridge
canonicalRootBridgeP7 = mkRootBridge (Ref.mkSSPPrimeLane369Refinement TP.p7 Ref.root) 3 "p7"

canonicalRootBridgeP11 :
  SSPPrimeLane369PAdicBridge
canonicalRootBridgeP11 = mkRootBridge (Ref.mkSSPPrimeLane369Refinement TP.p11 Ref.root) 4 "p11"

canonicalRootBridgeP13 :
  SSPPrimeLane369PAdicBridge
canonicalRootBridgeP13 = mkRootBridge (Ref.mkSSPPrimeLane369Refinement TP.p13 Ref.root) 5 "p13"

canonicalRootBridgeP17 :
  SSPPrimeLane369PAdicBridge
canonicalRootBridgeP17 = mkRootBridge (Ref.mkSSPPrimeLane369Refinement TP.p17 Ref.root) 6 "p17"

canonicalRootBridgeP19 :
  SSPPrimeLane369PAdicBridge
canonicalRootBridgeP19 = mkRootBridge (Ref.mkSSPPrimeLane369Refinement TP.p19 Ref.root) 7 "p19"

canonicalRootBridgeP23 :
  SSPPrimeLane369PAdicBridge
canonicalRootBridgeP23 = mkRootBridge (Ref.mkSSPPrimeLane369Refinement TP.p23 Ref.root) 8 "p23"

canonicalRootBridgeP29 :
  SSPPrimeLane369PAdicBridge
canonicalRootBridgeP29 = mkRootBridge (Ref.mkSSPPrimeLane369Refinement TP.p29 Ref.root) 9 "p29"

canonicalRootBridgeP31 :
  SSPPrimeLane369PAdicBridge
canonicalRootBridgeP31 = mkRootBridge (Ref.mkSSPPrimeLane369Refinement TP.p31 Ref.root) 10 "p31"

canonicalRootBridgeP41 :
  SSPPrimeLane369PAdicBridge
canonicalRootBridgeP41 = mkRootBridge (Ref.mkSSPPrimeLane369Refinement TP.p41 Ref.root) 11 "p41"

canonicalRootBridgeP47 :
  SSPPrimeLane369PAdicBridge
canonicalRootBridgeP47 = mkRootBridge (Ref.mkSSPPrimeLane369Refinement TP.p47 Ref.root) 12 "p47"

canonicalRootBridgeP59 :
  SSPPrimeLane369PAdicBridge
canonicalRootBridgeP59 = mkRootBridge (Ref.mkSSPPrimeLane369Refinement TP.p59 Ref.root) 13 "p59"

canonicalRootBridgeP71 :
  SSPPrimeLane369PAdicBridge
canonicalRootBridgeP71 = mkRootBridge (Ref.mkSSPPrimeLane369Refinement TP.p71 Ref.root) 14 "p71"

canonicalRootBridgeCarrierTuple :
  GL.Vec15 Carrier.PAdicCarrierCoordinate
canonicalRootBridgeCarrierTuple =
  GL.v15
    (bridge canonicalRootBridgeP2)
    (bridge canonicalRootBridgeP3)
    (bridge canonicalRootBridgeP5)
    (bridge canonicalRootBridgeP7)
    (bridge canonicalRootBridgeP11)
    (bridge canonicalRootBridgeP13)
    (bridge canonicalRootBridgeP17)
    (bridge canonicalRootBridgeP19)
    (bridge canonicalRootBridgeP23)
    (bridge canonicalRootBridgeP29)
    (bridge canonicalRootBridgeP31)
    (bridge canonicalRootBridgeP41)
    (bridge canonicalRootBridgeP47)
    (bridge canonicalRootBridgeP59)
    (bridge canonicalRootBridgeP71)

  where
    bridge :
      SSPPrimeLane369PAdicBridge →
      Carrier.PAdicCarrierCoordinate
    bridge = coordinate

canonicalRootBridgeCarrierTupleIsCanonical :
  canonicalRootBridgeCarrierTuple
  ≡
  Carrier.canonicalVec15PAdicCarrierTuple
canonicalRootBridgeCarrierTupleIsCanonical = refl

canonicalRootBridgeLaneTuple :
  GL.Vec15 (Forest.LaneDepthCarrier SSPPrimeLane369PAdicBridge)
canonicalRootBridgeLaneTuple =
  GL.v15
    (Forest.mkLaneDepthCarrier zero canonicalRootBridgeP2)
    (Forest.mkLaneDepthCarrier zero canonicalRootBridgeP3)
    (Forest.mkLaneDepthCarrier zero canonicalRootBridgeP5)
    (Forest.mkLaneDepthCarrier zero canonicalRootBridgeP7)
    (Forest.mkLaneDepthCarrier zero canonicalRootBridgeP11)
    (Forest.mkLaneDepthCarrier zero canonicalRootBridgeP13)
    (Forest.mkLaneDepthCarrier zero canonicalRootBridgeP17)
    (Forest.mkLaneDepthCarrier zero canonicalRootBridgeP19)
    (Forest.mkLaneDepthCarrier zero canonicalRootBridgeP23)
    (Forest.mkLaneDepthCarrier zero canonicalRootBridgeP29)
    (Forest.mkLaneDepthCarrier zero canonicalRootBridgeP31)
    (Forest.mkLaneDepthCarrier zero canonicalRootBridgeP41)
    (Forest.mkLaneDepthCarrier zero canonicalRootBridgeP47)
    (Forest.mkLaneDepthCarrier zero canonicalRootBridgeP59)
    (Forest.mkLaneDepthCarrier zero canonicalRootBridgeP71)

canonicalRootBridgeForest :
  Forest.FifteenSSP369Forest SSPPrimeLane369PAdicBridge
canonicalRootBridgeForest =
  Forest.mkFifteenSSP369Forest
    zero
    TP.trackedPrimeVec15
    canonicalRootBridgeLaneTuple
    refl

canonicalRootBridgeForestDepth :
  Forest.forestDepth canonicalRootBridgeForest ≡ zero
canonicalRootBridgeForestDepth = refl

canonicalRootBridgeForestLaneOrder :
  Forest.forestLaneOrder canonicalRootBridgeForest ≡ TP.trackedPrimeVec15
canonicalRootBridgeForestLaneOrder = refl

canonicalRootBridgeForestLaneOrderIsCanonical :
  Forest.forestLaneOrderIsCanonical canonicalRootBridgeForest ≡ refl
canonicalRootBridgeForestLaneOrderIsCanonical = refl

canonicalBridgeSurfaceStatement : String
canonicalBridgeSurfaceStatement =
  "This module records the finite depth-address-to-p-adic tuple bridge only; it does not construct an analytic p-adic completion, an adelic ring, or any promoted closure."
