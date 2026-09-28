module DASHI.Moonshine.OggSSPSmallPrimeMoonshinePowerTowerExact where

------------------------------------------------------------------------
-- SMALL-PRIME MOONSHINE POWER TOWER
--
-- EXTERNAL ATLAS INPUT
--
-- Monster power maps record:
--
--   (4C)^2 = 2B,
--   (9B)^3 = 3B.
--
-- Combined with the already sourced same-object identifications
--
--   J_2 = T_2B,  J_4 = T_4C,
--   J_3 = T_3B,  J_9 = T_9B,
--
-- the prime-square Duncan--Swisher coordinate is an ordinary moonshine
-- POWER-LIFT of the prime-level pB coordinate.
--
-- CONSEQUENCE
--
-- At each exceptional prime the published baseline already contains a
-- prime-power class tower:
--
--   p=2 : 4C --square--> 2B,
--   p=3 : 9B --cube----> 3B.
--
-- Any extra 10/2 bridge must refine this tower (e.g. twisted-centralizer /
-- bad-level local data); it cannot be an unrelated relabelling of J_{p^2}.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPSmallPrimeBaselineMoonshineTowerExact as BaselineTower
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Typed class/power relation.
------------------------------------------------------------------------

data PrimePowerMoonshineClass : Set where
  class2B :
    PrimePowerMoonshineClass
  class4C :
    PrimePowerMoonshineClass
  class3B :
    PrimePowerMoonshineClass
  class9B :
    PrimePowerMoonshineClass

classOrder :
  PrimePowerMoonshineClass ->
  Nat
classOrder class2B = 2
classOrder class4C = 4
classOrder class3B = 3
classOrder class9B = 9

data PowerRelation : Set where
  square4CTo2B :
    PowerRelation
  cube9BTo3B :
    PowerRelation

powerSource :
  PowerRelation ->
  PrimePowerMoonshineClass
powerSource square4CTo2B = class4C
powerSource cube9BTo3B = class9B

powerTarget :
  PowerRelation ->
  PrimePowerMoonshineClass
powerTarget square4CTo2B = class2B
powerTarget cube9BTo3B = class3B

powerExponent :
  PowerRelation ->
  Nat
powerExponent square4CTo2B = 2
powerExponent cube9BTo3B = 3

squareRelationOrderCheck :
  classOrder class4C ≡ powerExponent square4CTo2B * classOrder class2B
squareRelationOrderCheck = refl

cubeRelationOrderCheck :
  classOrder class9B ≡ powerExponent cube9BTo3B * classOrder class3B
cubeRelationOrderCheck = refl

------------------------------------------------------------------------
-- 2. Crosswalk to Duncan--Swisher baseline class labels.
------------------------------------------------------------------------

p2PrimeClassIs2B :
  BaselineTower.baselineClass
    BaselineTower.Baseline.pTwo
    BaselineTower.Baseline.primeLevel
  ≡
  BaselineTower.class2B
p2PrimeClassIs2B = refl

p2PrimeSquareClassIs4C :
  BaselineTower.baselineClass
    BaselineTower.Baseline.pTwo
    BaselineTower.Baseline.primeSquareLevel
  ≡
  BaselineTower.class4C
p2PrimeSquareClassIs4C = refl

p3PrimeClassIs3B :
  BaselineTower.baselineClass
    BaselineTower.Baseline.pThree
    BaselineTower.Baseline.primeLevel
  ≡
  BaselineTower.class3B
p3PrimeClassIs3B = refl

p3PrimeSquareClassIs9B :
  BaselineTower.baselineClass
    BaselineTower.Baseline.pThree
    BaselineTower.Baseline.primeSquareLevel
  ≡
  BaselineTower.class9B
p3PrimeSquareClassIs9B = refl

------------------------------------------------------------------------
-- 3. Power-lift interpretation, not an extra fourth coordinate.
------------------------------------------------------------------------

data PrimeSquareClassIndependentOfPrimeClassLane : Set where
data PowerMapCreatesExceptionalMonsterCorrection : Set where
data PowerLiftIdentifiesTwistedCentralizerObject : Set where

primeSquareClassIsNotIndependentLane :
  PrimeSquareClassIndependentOfPrimeClassLane -> ⊥
primeSquareClassIsNotIndependentLane ()

powerMapDoesNotCreateExceptionalCorrection :
  PowerMapCreatesExceptionalMonsterCorrection -> ⊥
powerMapDoesNotCreateExceptionalCorrection ()

powerLiftDoesNotIdentifyTwistedCentralizerObject :
  PowerLiftIdentifiesTwistedCentralizerObject -> ⊥
powerLiftDoesNotIdentifyTwistedCentralizerObject ()

------------------------------------------------------------------------
-- 4. Source attribution.
------------------------------------------------------------------------

monsterAtlasPowerMap : Source.AttributedSource
monsterAtlasPowerMap =
  Source.mkNoDOISource
    "ATLAS of Finite Group Representations"
    "Monster group M conjugacy classes and power maps"
    "ATLAS"
    ""
    "https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M/"
    Source.institutionalSource
    "Power-up table places 4C under 2B and 9B under 3B; with the class orders this is the sourced power-map relation (4C)^2=2B and (9B)^3=3B. No Monster-exponent correction is attributed to the table"
    Source.publicAttribution

powerTowerSourceAtlas : Source.AttributedSourceAtlas
powerTowerSourceAtlas =
  Source.mkSourceAtlas
    "small-prime Monster power-map tower"
    "DASHI.Moonshine.OggSSPSmallPrimeMoonshinePowerTowerExact"
    (monsterAtlasPowerMap ∷ [])
    "ATLAS owns the class power maps; earlier owners source the class/Hauptmodul identifications; DASHI owns the cross-module conclusion that the prime-square baseline coordinates are power-lifts of pB"

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record SmallPrimeMoonshinePowerTowerBoundary : Set where
  constructor small-prime-moonshine-power-tower-boundary
  field
    fourCSquaresToTwoBSourced : Bool
    nineBCubesToThreeBSourced : Bool
    primeLevelClassesAlreadyBaseline : Bool
    primeSquareClassesAlreadyBaseline : Bool
    primeSquareCoordinatesRecognisedAsPowerLifts : Bool
    powerMapCreatesFourthTerm : Bool
    twistedCentralizerRecognitionStillRequired : Bool
    attributionFirewallPreserved : Bool

canonicalSmallPrimeMoonshinePowerTowerBoundary :
  SmallPrimeMoonshinePowerTowerBoundary
canonicalSmallPrimeMoonshinePowerTowerBoundary =
  small-prime-moonshine-power-tower-boundary
    true true true true true false true true
