module DASHI.Foundations.FifteenSSP369Forest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import MonsterOntos using (SSP)
open import DASHI.TrackedPrimes using (trackedPrimeList; trackedPrimeVec15)
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

------------------------------------------------------------------------
-- A depth-refined lane carrier and its 15-lane forest product.
--
-- The forest keeps the canonical tracked 15-prime order visible and carries
-- one depth-tagged lane state per prime lane.

record LaneDepthCarrier (A : Set) : Set where
  constructor mkLaneDepthCarrier
  field
    laneDepth : Nat
    lanePayload : A

open LaneDepthCarrier public

record FifteenSSP369Forest (A : Set) : Set where
  constructor mkFifteenSSP369Forest
  field
    forestDepth : Nat
    forestLaneOrder : Vec15 SSP
    forestLanes : Vec15 (LaneDepthCarrier A)
    forestLaneOrderIsCanonical : forestLaneOrder ≡ trackedPrimeVec15

open FifteenSSP369Forest public

------------------------------------------------------------------------
-- Canonical tracked prime order.

canonicalTrackedPrimeOrderList : List SSP
canonicalTrackedPrimeOrderList = trackedPrimeList

canonicalTrackedPrimeOrderListIsCanonical :
  canonicalTrackedPrimeOrderList ≡ trackedPrimeList
canonicalTrackedPrimeOrderListIsCanonical = refl

canonicalTrackedPrimeOrderVec15 : Vec15 SSP
canonicalTrackedPrimeOrderVec15 = trackedPrimeVec15

canonicalTrackedPrimeOrderVec15IsCanonical :
  canonicalTrackedPrimeOrderVec15 ≡ trackedPrimeVec15
canonicalTrackedPrimeOrderVec15IsCanonical = refl

------------------------------------------------------------------------
-- Canonical lane and forest constructors.

constantLaneDepthCarrier : {A : Set} → Nat → A → LaneDepthCarrier A
constantLaneDepthCarrier d a = mkLaneDepthCarrier d a

constantForest : {A : Set} → Nat → A → FifteenSSP369Forest A
constantForest d a =
  mkFifteenSSP369Forest
    d
    trackedPrimeVec15
    (mkVec15
      (constantLaneDepthCarrier d a)
      (constantLaneDepthCarrier d a)
      (constantLaneDepthCarrier d a)
      (constantLaneDepthCarrier d a)
      (constantLaneDepthCarrier d a)
      (constantLaneDepthCarrier d a)
      (constantLaneDepthCarrier d a)
      (constantLaneDepthCarrier d a)
      (constantLaneDepthCarrier d a)
      (constantLaneDepthCarrier d a)
      (constantLaneDepthCarrier d a)
      (constantLaneDepthCarrier d a)
      (constantLaneDepthCarrier d a)
      (constantLaneDepthCarrier d a)
      (constantLaneDepthCarrier d a))
    refl

rootForest : {A : Set} → A → FifteenSSP369Forest A
rootForest = constantForest zero

rootForestDepth : {A : Set} (a : A) → forestDepth (rootForest a) ≡ zero
rootForestDepth a = refl

rootForestLaneOrder : {A : Set} (a : A) → forestLaneOrder (rootForest a) ≡ trackedPrimeVec15
rootForestLaneOrder a = refl

canonicalZeroForest : FifteenSSP369Forest Nat
canonicalZeroForest = rootForest zero

canonicalRootForest : FifteenSSP369Forest Nat
canonicalRootForest = canonicalZeroForest

canonicalZeroForestDepth : forestDepth canonicalZeroForest ≡ zero
canonicalZeroForestDepth = refl

canonicalRootForestDepth : forestDepth canonicalRootForest ≡ zero
canonicalRootForestDepth = refl

canonicalZeroForestLaneOrder : forestLaneOrder canonicalZeroForest ≡ trackedPrimeVec15
canonicalZeroForestLaneOrder = refl

------------------------------------------------------------------------
-- Lane projectors.

p2LaneCarrier : {A : Set} → FifteenSSP369Forest A → LaneDepthCarrier A
p2LaneCarrier (mkFifteenSSP369Forest _ _ (mkVec15 l2 l3 l5 l7 l11 l13 l17 l19 l23 l29 l31 l41 l47 l59 l71) _) =
  l2

p3LaneCarrier : {A : Set} → FifteenSSP369Forest A → LaneDepthCarrier A
p3LaneCarrier (mkFifteenSSP369Forest _ _ (mkVec15 l2 l3 l5 l7 l11 l13 l17 l19 l23 l29 l31 l41 l47 l59 l71) _) =
  l3

p5LaneCarrier : {A : Set} → FifteenSSP369Forest A → LaneDepthCarrier A
p5LaneCarrier (mkFifteenSSP369Forest _ _ (mkVec15 l2 l3 l5 l7 l11 l13 l17 l19 l23 l29 l31 l41 l47 l59 l71) _) =
  l5

p71LaneCarrier : {A : Set} → FifteenSSP369Forest A → LaneDepthCarrier A
p71LaneCarrier (mkFifteenSSP369Forest _ _ (mkVec15 l2 l3 l5 l7 l11 l13 l17 l19 l23 l29 l31 l41 l47 l59 l71) _) =
  l71

p2LaneDepth : {A : Set} → FifteenSSP369Forest A → Nat
p2LaneDepth f = laneDepth (p2LaneCarrier f)

p2LanePayload : {A : Set} → FifteenSSP369Forest A → A
p2LanePayload f = lanePayload (p2LaneCarrier f)

p3LanePayload : {A : Set} → FifteenSSP369Forest A → A
p3LanePayload f = lanePayload (p3LaneCarrier f)

p5LaneDepth : {A : Set} → FifteenSSP369Forest A → Nat
p5LaneDepth f = laneDepth (p5LaneCarrier f)

p71LanePayload : {A : Set} → FifteenSSP369Forest A → A
p71LanePayload f = lanePayload (p71LaneCarrier f)

p71LaneDepth : {A : Set} → FifteenSSP369Forest A → Nat
p71LaneDepth f = laneDepth (p71LaneCarrier f)

------------------------------------------------------------------------
-- Concrete examples.

p2DepthOnZeroForest : p2LaneDepth canonicalZeroForest ≡ zero
p2DepthOnZeroForest = refl

p3PayloadOnZeroForest : p3LanePayload canonicalZeroForest ≡ zero
p3PayloadOnZeroForest = refl

p5DepthOnZeroForest : p5LaneDepth canonicalZeroForest ≡ zero
p5DepthOnZeroForest = refl

p71PayloadOnZeroForest : p71LanePayload canonicalZeroForest ≡ zero
p71PayloadOnZeroForest = refl

exampleOneForest : FifteenSSP369Forest Nat
exampleOneForest = constantForest (suc zero) (suc zero)

exampleOneForestDepth : forestDepth exampleOneForest ≡ suc zero
exampleOneForestDepth = refl

exampleOneForestP2Payload : p2LanePayload exampleOneForest ≡ suc zero
exampleOneForestP2Payload = refl

exampleOneForestP71Depth : p71LaneDepth exampleOneForest ≡ suc zero
exampleOneForestP71Depth = refl
