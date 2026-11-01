module DASHI.Foundations.FifteenSSPSurface where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import DASHI.Foundations.SSPTritCarrier using
  ( SSPTrit
  ; sspNegOne
  ; sspZero
  ; sspPosOne
  )
open import DASHI.TrackedPrimes using (trackedPrimeList; trackedPrimeVec15)
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

------------------------------------------------------------------------
-- Typed 15-lane SSP trit surface.
--
-- The carrier is a Vec15 Trit over the canonical 15 SSP prime lanes:
--   p2, p3, p5, p7, p11, p13, p17, p19, p23, p29, p31, p41, p47, p59, p71.

FifteenSSPTritCarrier : Set
FifteenSSPTritCarrier = Vec15 SSPTrit

canonicalLaneOrderList : List SSP
canonicalLaneOrderList = trackedPrimeList

canonicalLaneOrderVec15 : Vec15 SSP
canonicalLaneOrderVec15 = trackedPrimeVec15

canonicalLaneOrderListIsCanonical :
  canonicalLaneOrderList
  ≡
  (p2 ∷ p3 ∷ p5 ∷ p7 ∷ p11 ∷ p13 ∷ p17 ∷ p19 ∷ p23 ∷ p29 ∷ p31 ∷ p41 ∷ p47 ∷ p59 ∷ p71 ∷ [])
canonicalLaneOrderListIsCanonical = refl

canonicalLaneOrderVec15IsCanonical :
  canonicalLaneOrderVec15
  ≡
  mkVec15 p2 p3 p5 p7 p11 p13 p17 p19 p23 p29 p31 p41 p47 p59 p71
canonicalLaneOrderVec15IsCanonical = refl

------------------------------------------------------------------------
-- Concrete surfaces over the canonical lane order.

zeroFifteenSSPTritCarrier : FifteenSSPTritCarrier
zeroFifteenSSPTritCarrier =
  mkVec15
    sspZero sspZero sspZero sspZero sspZero
    sspZero sspZero sspZero sspZero sspZero
    sspZero sspZero sspZero sspZero sspZero

positiveFifteenSSPTritCarrier : FifteenSSPTritCarrier
positiveFifteenSSPTritCarrier =
  mkVec15
    sspPosOne sspPosOne sspPosOne sspPosOne sspPosOne
    sspPosOne sspPosOne sspPosOne sspPosOne sspPosOne
    sspPosOne sspPosOne sspPosOne sspPosOne sspPosOne

negativeFifteenSSPTritCarrier : FifteenSSPTritCarrier
negativeFifteenSSPTritCarrier =
  mkVec15
    sspNegOne sspNegOne sspNegOne sspNegOne sspNegOne
    sspNegOne sspNegOne sspNegOne sspNegOne sspNegOne
    sspNegOne sspNegOne sspNegOne sspNegOne sspNegOne

exampleFifteenSSPTritCarrier : FifteenSSPTritCarrier
exampleFifteenSSPTritCarrier =
  mkVec15
    sspNegOne sspZero sspPosOne sspNegOne sspZero
    sspPosOne sspNegOne sspZero sspPosOne sspNegOne
    sspZero sspPosOne sspNegOne sspZero sspPosOne

record FifteenSSPSurface : Set where
  constructor mkFifteenSSPSurface
  field
    trits : FifteenSSPTritCarrier
    laneOrderList : List SSP
    laneOrderVec15 : Vec15 SSP
    laneOrderListIsCanonical : laneOrderList ≡ canonicalLaneOrderList
    laneOrderVec15IsCanonical : laneOrderVec15 ≡ canonicalLaneOrderVec15

open FifteenSSPSurface public

canonicalZeroFifteenSSPSurface : FifteenSSPSurface
canonicalZeroFifteenSSPSurface =
  mkFifteenSSPSurface
    zeroFifteenSSPTritCarrier
    canonicalLaneOrderList
    canonicalLaneOrderVec15
    refl
    refl

canonicalPositiveFifteenSSPSurface : FifteenSSPSurface
canonicalPositiveFifteenSSPSurface =
  mkFifteenSSPSurface
    positiveFifteenSSPTritCarrier
    canonicalLaneOrderList
    canonicalLaneOrderVec15
    refl
    refl

canonicalNegativeFifteenSSPSurface : FifteenSSPSurface
canonicalNegativeFifteenSSPSurface =
  mkFifteenSSPSurface
    negativeFifteenSSPTritCarrier
    canonicalLaneOrderList
    canonicalLaneOrderVec15
    refl
    refl

canonicalExampleFifteenSSPSurface : FifteenSSPSurface
canonicalExampleFifteenSSPSurface =
  mkFifteenSSPSurface
    exampleFifteenSSPTritCarrier
    canonicalLaneOrderList
    canonicalLaneOrderVec15
    refl
    refl

------------------------------------------------------------------------
-- Lane projections.

p2Trit : FifteenSSPTritCarrier → SSPTrit
p2Trit (mkVec15 t2 t3 t5 t7 t11 t13 t17 t19 t23 t29 t31 t41 t47 t59 t71) = t2

p3Trit : FifteenSSPTritCarrier → SSPTrit
p3Trit (mkVec15 t2 t3 t5 t7 t11 t13 t17 t19 t23 t29 t31 t41 t47 t59 t71) = t3

p5Trit : FifteenSSPTritCarrier → SSPTrit
p5Trit (mkVec15 t2 t3 t5 t7 t11 t13 t17 t19 t23 t29 t31 t41 t47 t59 t71) = t5

p7Trit : FifteenSSPTritCarrier → SSPTrit
p7Trit (mkVec15 t2 t3 t5 t7 t11 t13 t17 t19 t23 t29 t31 t41 t47 t59 t71) = t7

p11Trit : FifteenSSPTritCarrier → SSPTrit
p11Trit (mkVec15 t2 t3 t5 t7 t11 t13 t17 t19 t23 t29 t31 t41 t47 t59 t71) = t11

p13Trit : FifteenSSPTritCarrier → SSPTrit
p13Trit (mkVec15 t2 t3 t5 t7 t11 t13 t17 t19 t23 t29 t31 t41 t47 t59 t71) = t13

p17Trit : FifteenSSPTritCarrier → SSPTrit
p17Trit (mkVec15 t2 t3 t5 t7 t11 t13 t17 t19 t23 t29 t31 t41 t47 t59 t71) = t17

p19Trit : FifteenSSPTritCarrier → SSPTrit
p19Trit (mkVec15 t2 t3 t5 t7 t11 t13 t17 t19 t23 t29 t31 t41 t47 t59 t71) = t19

p23Trit : FifteenSSPTritCarrier → SSPTrit
p23Trit (mkVec15 t2 t3 t5 t7 t11 t13 t17 t19 t23 t29 t31 t41 t47 t59 t71) = t23

p29Trit : FifteenSSPTritCarrier → SSPTrit
p29Trit (mkVec15 t2 t3 t5 t7 t11 t13 t17 t19 t23 t29 t31 t41 t47 t59 t71) = t29

p31Trit : FifteenSSPTritCarrier → SSPTrit
p31Trit (mkVec15 t2 t3 t5 t7 t11 t13 t17 t19 t23 t29 t31 t41 t47 t59 t71) = t31

p41Trit : FifteenSSPTritCarrier → SSPTrit
p41Trit (mkVec15 t2 t3 t5 t7 t11 t13 t17 t19 t23 t29 t31 t41 t47 t59 t71) = t41

p47Trit : FifteenSSPTritCarrier → SSPTrit
p47Trit (mkVec15 t2 t3 t5 t7 t11 t13 t17 t19 t23 t29 t31 t41 t47 t59 t71) = t47

p59Trit : FifteenSSPTritCarrier → SSPTrit
p59Trit (mkVec15 t2 t3 t5 t7 t11 t13 t17 t19 t23 t29 t31 t41 t47 t59 t71) = t59

p71Trit : FifteenSSPTritCarrier → SSPTrit
p71Trit (mkVec15 t2 t3 t5 t7 t11 t13 t17 t19 t23 t29 t31 t41 t47 t59 t71) = t71

projectLane : SSP → FifteenSSPSurface → SSPTrit
projectLane p s with p
... | p2  = p2Trit (trits s)
... | p3  = p3Trit (trits s)
... | p5  = p5Trit (trits s)
... | p7  = p7Trit (trits s)
... | p11 = p11Trit (trits s)
... | p13 = p13Trit (trits s)
... | p17 = p17Trit (trits s)
... | p19 = p19Trit (trits s)
... | p23 = p23Trit (trits s)
... | p29 = p29Trit (trits s)
... | p31 = p31Trit (trits s)
... | p41 = p41Trit (trits s)
... | p47 = p47Trit (trits s)
... | p59 = p59Trit (trits s)
... | p71 = p71Trit (trits s)

p2Surface : FifteenSSPSurface → SSPTrit
p2Surface = projectLane p2

p3Surface : FifteenSSPSurface → SSPTrit
p3Surface = projectLane p3

p5Surface : FifteenSSPSurface → SSPTrit
p5Surface = projectLane p5

p7Surface : FifteenSSPSurface → SSPTrit
p7Surface = projectLane p7

p11Surface : FifteenSSPSurface → SSPTrit
p11Surface = projectLane p11

p13Surface : FifteenSSPSurface → SSPTrit
p13Surface = projectLane p13

p17Surface : FifteenSSPSurface → SSPTrit
p17Surface = projectLane p17

p19Surface : FifteenSSPSurface → SSPTrit
p19Surface = projectLane p19

p23Surface : FifteenSSPSurface → SSPTrit
p23Surface = projectLane p23

p29Surface : FifteenSSPSurface → SSPTrit
p29Surface = projectLane p29

p31Surface : FifteenSSPSurface → SSPTrit
p31Surface = projectLane p31

p41Surface : FifteenSSPSurface → SSPTrit
p41Surface = projectLane p41

p47Surface : FifteenSSPSurface → SSPTrit
p47Surface = projectLane p47

p59Surface : FifteenSSPSurface → SSPTrit
p59Surface = projectLane p59

p71Surface : FifteenSSPSurface → SSPTrit
p71Surface = projectLane p71

surfaceAsVec15 : FifteenSSPSurface → FifteenSSPTritCarrier
surfaceAsVec15 = trits

surfaceLaneOrderAsList : FifteenSSPSurface → List SSP
surfaceLaneOrderAsList = laneOrderList

surfaceLaneOrderAsVec15 : FifteenSSPSurface → Vec15 SSP
surfaceLaneOrderAsVec15 = laneOrderVec15

------------------------------------------------------------------------
-- Small canonical equalities for the tracked prime lane order.

trackedPrimeListIsCanonical :
  trackedPrimeList
  ≡
  canonicalLaneOrderList
trackedPrimeListIsCanonical = refl

trackedPrimeVec15IsCanonical :
  trackedPrimeVec15
  ≡
  canonicalLaneOrderVec15
trackedPrimeVec15IsCanonical = refl

zeroSurfaceLaneOrderIsCanonicalList :
  laneOrderList canonicalZeroFifteenSSPSurface
  ≡
  canonicalLaneOrderList
zeroSurfaceLaneOrderIsCanonicalList =
  laneOrderListIsCanonical canonicalZeroFifteenSSPSurface

zeroSurfaceLaneOrderIsCanonicalVec15 :
  laneOrderVec15 canonicalZeroFifteenSSPSurface
  ≡
  canonicalLaneOrderVec15
zeroSurfaceLaneOrderIsCanonicalVec15 =
  laneOrderVec15IsCanonical canonicalZeroFifteenSSPSurface

positiveSurfaceLaneOrderIsCanonicalList :
  laneOrderList canonicalPositiveFifteenSSPSurface
  ≡
  canonicalLaneOrderList
positiveSurfaceLaneOrderIsCanonicalList =
  laneOrderListIsCanonical canonicalPositiveFifteenSSPSurface

negativeSurfaceLaneOrderIsCanonicalVec15 :
  laneOrderVec15 canonicalNegativeFifteenSSPSurface
  ≡
  canonicalLaneOrderVec15
negativeSurfaceLaneOrderIsCanonicalVec15 =
  laneOrderVec15IsCanonical canonicalNegativeFifteenSSPSurface

exampleSurfaceLaneOrderIsCanonicalList :
  laneOrderList canonicalExampleFifteenSSPSurface
  ≡
  canonicalLaneOrderList
exampleSurfaceLaneOrderIsCanonicalList =
  laneOrderListIsCanonical canonicalExampleFifteenSSPSurface

exampleSurfaceLaneOrderIsCanonicalVec15 :
  laneOrderVec15 canonicalExampleFifteenSSPSurface
  ≡
  canonicalLaneOrderVec15
exampleSurfaceLaneOrderIsCanonicalVec15 =
  laneOrderVec15IsCanonical canonicalExampleFifteenSSPSurface
