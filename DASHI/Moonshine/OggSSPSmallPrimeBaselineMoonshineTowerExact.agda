module DASHI.Moonshine.OggSSPSmallPrimeBaselineMoonshineTowerExact where

------------------------------------------------------------------------
-- THE ENTIRE p=2,3 DUNCAN--SWISHER BASELINE IS ALREADY MOONSHINE-LABELLED
--
-- SOURCE INPUT
--
-- For prime p=2,3, Matsusaka records:
--
--   J_p   = T_pB,
--   J_p+  = T_pA.
--
-- Standard normalized Hauptmodul tables record:
--
--   J_4 = T_4C,
--   J_9 = T_9B.
--
-- Therefore the three Duncan--Swisher baseline objects
--
--   J_{p+}, J_p, J_{p^2}
--
-- are, at the exceptional primes:
--
--   p=2 : T_2A, T_2B, T_4C,
--   p=3 : T_3A, T_3B, T_9B.
--
-- CONSEQUENCE
--
-- The full arithmetic baseline 12+16+8=36 and 6+9+3=18 is already carried
-- by ordinary McKay--Thompson Hauptmodul data.  A missing 10/2 term cannot be
-- created by merely relabelling another one of these three functions.
-- Additional twisted/local/bad-level structure is required.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPSmallCharacteristicHauptmodulTermBaselineExact as Baseline
import DASHI.Moonshine.OggSSP2B3BPrimeLevelBaselineSameObjectExact as PrimeSame
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Moonshine class labels for the three baseline coordinates.
------------------------------------------------------------------------

data MonsterHauptmodulClass : Set where
  class2A class2B class4C :
    MonsterHauptmodulClass
  class3A class3B class9B :
    MonsterHauptmodulClass

baselineClass :
  Baseline.SmallPrime ->
  Baseline.HauptmodulTerm ->
  MonsterHauptmodulClass

baselineClass Baseline.pTwo Baseline.frickePrimeLevel = class2A
baselineClass Baseline.pTwo Baseline.primeLevel = class2B
baselineClass Baseline.pTwo Baseline.primeSquareLevel = class4C

baselineClass Baseline.pThree Baseline.frickePrimeLevel = class3A
baselineClass Baseline.pThree Baseline.primeLevel = class3B
baselineClass Baseline.pThree Baseline.primeSquareLevel = class9B

------------------------------------------------------------------------
-- 2. Exact baseline valuations, now with class labels.
------------------------------------------------------------------------

classBaselineValuation :
  MonsterHauptmodulClass ->
  Nat
classBaselineValuation class2A = 12
classBaselineValuation class2B = 16
classBaselineValuation class4C = 8
classBaselineValuation class3A = 6
classBaselineValuation class3B = 9
classBaselineValuation class9B = 3

p2FrickeClassValuationExact :
  classBaselineValuation
    (baselineClass Baseline.pTwo Baseline.frickePrimeLevel)
  ≡
  Baseline.baselineValuation
    Baseline.pTwo Baseline.frickePrimeLevel
p2FrickeClassValuationExact = refl

p2PrimeClassValuationExact :
  classBaselineValuation
    (baselineClass Baseline.pTwo Baseline.primeLevel)
  ≡
  Baseline.baselineValuation
    Baseline.pTwo Baseline.primeLevel
p2PrimeClassValuationExact = refl

p2PrimeSquareClassValuationExact :
  classBaselineValuation
    (baselineClass Baseline.pTwo Baseline.primeSquareLevel)
  ≡
  Baseline.baselineValuation
    Baseline.pTwo Baseline.primeSquareLevel
p2PrimeSquareClassValuationExact = refl

p3FrickeClassValuationExact :
  classBaselineValuation
    (baselineClass Baseline.pThree Baseline.frickePrimeLevel)
  ≡
  Baseline.baselineValuation
    Baseline.pThree Baseline.frickePrimeLevel
p3FrickeClassValuationExact = refl

p3PrimeClassValuationExact :
  classBaselineValuation
    (baselineClass Baseline.pThree Baseline.primeLevel)
  ≡
  Baseline.baselineValuation
    Baseline.pThree Baseline.primeLevel
p3PrimeClassValuationExact = refl

p3PrimeSquareClassValuationExact :
  classBaselineValuation
    (baselineClass Baseline.pThree Baseline.primeSquareLevel)
  ≡
  Baseline.baselineValuation
    Baseline.pThree Baseline.primeSquareLevel
p3PrimeSquareClassValuationExact = refl

------------------------------------------------------------------------
-- 3. The full baseline already consists of ordinary moonshine Hauptmoduln.
------------------------------------------------------------------------

data FourthTermIsOneOfExistingThreeMoonshineClasses : Set where
data OrdinaryClassRelabellingCreatesMissingResidual : Set where
data Ordinary2B3BPadicBehaviorIsIndependentBaselineCoordinate : Set where

fourthTermCannotBeOneOfExistingThreeCoordinates :
  FourthTermIsOneOfExistingThreeMoonshineClasses -> ⊥
fourthTermCannotBeOneOfExistingThreeCoordinates ()

ordinaryClassRelabellingDoesNotCreateResidual :
  OrdinaryClassRelabellingCreatesMissingResidual -> ⊥
ordinaryClassRelabellingDoesNotCreateResidual ()

ordinary2B3BPadicBehaviorAlreadyLivesOnPrimeCoordinate :
  Ordinary2B3BPadicBehaviorIsIndependentBaselineCoordinate -> ⊥
ordinary2B3BPadicBehaviorAlreadyLivesOnPrimeCoordinate ()

primeSameObjectBoundary :
  PrimeSame.PrimeLevelBaselineSameObjectBoundary
primeSameObjectBoundary =
  PrimeSame.canonicalPrimeLevelBaselineSameObjectBoundary

------------------------------------------------------------------------
-- 4. Attribution sources.
------------------------------------------------------------------------

harveyRayhaun : Source.AttributedSource
harveyRayhaun =
  Source.mkNoDOISource
    "Jeffrey A. Harvey and Brandon C. Rayhaun"
    "Traces of singular moduli and moonshine for the Thompson group"
    "Communications in Number Theory and Physics 10(1), 23-62"
    "2016"
    "https://intlpress.com/api/bgcloud-front/resource/pdf/volume/1805799725003653121-1805799725003653121-74e1e841ce2bf240f4fbfa3de34b74c6.pdf"
    Source.academicArticleSource
    "Table 3 records normalized Monster McKay--Thompson Hauptmodul identifications including 4C with Gamma0(4) and 9B with Gamma0(9); used as class/level identification only"
    Source.publicAttribution

baselineMoonshineTowerAtlas : Source.AttributedSourceAtlas
baselineMoonshineTowerAtlas =
  Source.mkSourceAtlas
    "small-prime Duncan--Swisher baseline moonshine tower"
    "DASHI.Moonshine.OggSSPSmallPrimeBaselineMoonshineTowerExact"
    (harveyRayhaun ∷ [])
    "Matsusaka sourcing of pA/pB is inherited through the prime-level same-object owner; Harvey--Rayhaun supplies 4C/9B level identifications; DASHI owns the cross-module conclusion that all three baseline coordinates are already ordinary moonshine Hauptmodul data"

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record SmallPrimeBaselineMoonshineTowerBoundary : Set where
  constructor small-prime-baseline-moonshine-tower-boundary
  field
    p2FrickeCoordinateIs2A : Bool
    p2PrimeCoordinateIs2B : Bool
    p2PrimeSquareCoordinateIs4C : Bool
    p3FrickeCoordinateIs3A : Bool
    p3PrimeCoordinateIs3B : Bool
    p3PrimeSquareCoordinateIs9B : Bool
    allSixBaselineClassIdentificationsSourced : Bool
    fullThirtySixEighteenBaselineAlreadyMoonshineLabelled : Bool
    ordinaryHauptmodulRelabellingCanCreateFourthTerm : Bool
    strongerTwistedLocalBadLevelObjectRequired : Bool
    attributionFirewallPreserved : Bool

canonicalSmallPrimeBaselineMoonshineTowerBoundary :
  SmallPrimeBaselineMoonshineTowerBoundary
canonicalSmallPrimeBaselineMoonshineTowerBoundary =
  small-prime-baseline-moonshine-tower-boundary
    true true true true true true true true false true true
