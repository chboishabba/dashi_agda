module DASHI.Foundations.BalancedTernaryAntipodal369OrbitHierarchyExact where

------------------------------------------------------------------------
-- BALANCED-TERNARY ANTIPODAL 3 / 9 / 27 ORBIT HIERARCHY
--
-- SOURCE / METHOD CALIBRATION
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Consolidate the already-owned antipodal 9- and 27-state quotients with the
-- missing rank-1 3-state quotient:
--
--   3  = 1 + 1*2  -> 2 orbit classes
--   9  = 1 + 4*2  -> 5 orbit classes
--   27 = 1 +13*2  ->14 orbit classes
--
-- The common geometry is one unique zero/fixed centre plus antipodal pairs.
-- This module does NOT claim that the Ogg/Monster residual arithmetic is
-- explained by these counts.  Domain recognition remains a separate theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Existing
import DASHI.Biology.TriadicKernelLiftQuotientExact as Kernel

------------------------------------------------------------------------
-- 1. Rank-1 quotient: 3 -> 2.
------------------------------------------------------------------------

data AntipodalClass3 : Set where
  centre3 : AntipodalClass3
  nonzero3 : AntipodalClass3

classifyAntipodal3 : SSP.SSPTrit -> AntipodalClass3
classifyAntipodal3 SSP.sspZero = centre3
classifyAntipodal3 SSP.sspNegOne = nonzero3
classifyAntipodal3 SSP.sspPosOne = nonzero3

classifyAntipodal3Invariant :
  (x : SSP.SSPTrit) ->
  classifyAntipodal3 (Existing.strictAntipode x)
  ≡ classifyAntipodal3 x
classifyAntipodal3Invariant SSP.sspNegOne = refl
classifyAntipodal3Invariant SSP.sspZero = refl
classifyAntipodal3Invariant SSP.sspPosOne = refl

antipodalClass3Count : Nat
antipodalClass3Count = 2

threeDecomposesAsCentrePlusOnePair :
  3 ≡ 1 + 1 * 2
threeDecomposesAsCentrePlusOnePair = refl

antipodalClass3CountIsTwo :
  antipodalClass3Count ≡ 2
antipodalClass3CountIsTwo = refl

------------------------------------------------------------------------
-- 2. Existing rank-2 and rank-3 counts.
------------------------------------------------------------------------

antipodalClass9Count : Nat
antipodalClass9Count = Existing.antipodalClass9Count

antipodalClass27Count : Nat
antipodalClass27Count = Existing.antipodalClass27Count

antipodalClass9CountIsFive :
  antipodalClass9Count ≡ 5
antipodalClass9CountIsFive = Existing.antipodalClass9CountIsFive

antipodalClass27CountIsFourteen :
  antipodalClass27Count ≡ 14
antipodalClass27CountIsFourteen = Existing.antipodalClass27CountIsFourteen

nineDecomposesAsCentrePlusFourPairs :
  9 ≡ 1 + 4 * 2
nineDecomposesAsCentrePlusFourPairs =
  Existing.nineDecomposesAsCentrePlusFourPairs

twentySevenDecomposesAsCentrePlusThirteenPairs :
  27 ≡ 1 + 13 * 2
twentySevenDecomposesAsCentrePlusThirteenPairs =
  Existing.ternaryCubeCountDecomposesAsCentrePlusThirteenPairs

------------------------------------------------------------------------
-- 3. One finite hierarchy surface.
------------------------------------------------------------------------

data TernaryAntipodalRank : Set where
  rank1 rank2 rank3 : TernaryAntipodalRank

rawCarrierCount : TernaryAntipodalRank -> Nat
rawCarrierCount rank1 = 3
rawCarrierCount rank2 = 9
rawCarrierCount rank3 = 27

pairedOrbitCount : TernaryAntipodalRank -> Nat
pairedOrbitCount rank1 = 1
pairedOrbitCount rank2 = 4
pairedOrbitCount rank3 = 13

quotientOrbitCount : TernaryAntipodalRank -> Nat
quotientOrbitCount rank1 = 2
quotientOrbitCount rank2 = 5
quotientOrbitCount rank3 = 14

rawCountIsCentrePlusPairs :
  (rank : TernaryAntipodalRank) ->
  rawCarrierCount rank ≡ 1 + pairedOrbitCount rank * 2
rawCountIsCentrePlusPairs rank1 = refl
rawCountIsCentrePlusPairs rank2 = refl
rawCountIsCentrePlusPairs rank3 = refl

quotientCountIsCentrePlusPairClasses :
  (rank : TernaryAntipodalRank) ->
  quotientOrbitCount rank ≡ 1 + pairedOrbitCount rank
quotientCountIsCentrePlusPairClasses rank1 = refl
quotientCountIsCentrePlusPairClasses rank2 = refl
quotientCountIsCentrePlusPairClasses rank3 = refl

rank1CountIsTwo : quotientOrbitCount rank1 ≡ 2
rank1CountIsTwo = refl

rank2CountIsFive : quotientOrbitCount rank2 ≡ 5
rank2CountIsFive = refl

rank3CountIsFourteen : quotientOrbitCount rank3 ≡ 14
rank3CountIsFourteen = refl

------------------------------------------------------------------------
-- 4. Exact rechart: existing Kernel NineOrbit <-> SSP antipodal rank-2 orbit.
--
-- This proves that the five-state object used in the p=2 lane is literally a
-- presentation of the already-owned global-antipode quotient geometry.
------------------------------------------------------------------------

kernelNineOrbitToAntipodal9 :
  Kernel.NineOrbit -> Existing.AntipodalClass9
kernelNineOrbitToAntipodal9 Kernel.zeroOrbit =
  Existing.centre9
kernelNineOrbitToAntipodal9 Kernel.firstAxisOrbit =
  Existing.firstAxis9
kernelNineOrbitToAntipodal9 Kernel.secondAxisOrbit =
  Existing.secondAxis9
kernelNineOrbitToAntipodal9 Kernel.equalSignOrbit =
  Existing.sameSignDiagonal9
kernelNineOrbitToAntipodal9 Kernel.oppositeSignOrbit =
  Existing.oppositeSignDiagonal9

antipodal9ToKernelNineOrbit :
  Existing.AntipodalClass9 -> Kernel.NineOrbit
antipodal9ToKernelNineOrbit Existing.centre9 =
  Kernel.zeroOrbit
antipodal9ToKernelNineOrbit Existing.firstAxis9 =
  Kernel.firstAxisOrbit
antipodal9ToKernelNineOrbit Existing.secondAxis9 =
  Kernel.secondAxisOrbit
antipodal9ToKernelNineOrbit Existing.sameSignDiagonal9 =
  Kernel.equalSignOrbit
antipodal9ToKernelNineOrbit Existing.oppositeSignDiagonal9 =
  Kernel.oppositeSignOrbit

kernelNineOrbitRoundTrip :
  (orbit : Kernel.NineOrbit) ->
  antipodal9ToKernelNineOrbit (kernelNineOrbitToAntipodal9 orbit) ≡ orbit
kernelNineOrbitRoundTrip Kernel.zeroOrbit = refl
kernelNineOrbitRoundTrip Kernel.firstAxisOrbit = refl
kernelNineOrbitRoundTrip Kernel.secondAxisOrbit = refl
kernelNineOrbitRoundTrip Kernel.equalSignOrbit = refl
kernelNineOrbitRoundTrip Kernel.oppositeSignOrbit = refl

antipodal9RoundTrip :
  (orbit : Existing.AntipodalClass9) ->
  kernelNineOrbitToAntipodal9 (antipodal9ToKernelNineOrbit orbit) ≡ orbit
antipodal9RoundTrip Existing.centre9 = refl
antipodal9RoundTrip Existing.firstAxis9 = refl
antipodal9RoundTrip Existing.secondAxis9 = refl
antipodal9RoundTrip Existing.sameSignDiagonal9 = refl
antipodal9RoundTrip Existing.oppositeSignDiagonal9 = refl

------------------------------------------------------------------------
-- 5. Exceptional residual target COUNT shape.
--
-- rank1 is the two-orbit target used at p=3.
-- p=2 retains a separate binary provenance/orientation sheet over rank2.
-- This is a target-shape statement only, not an arithmetic recognition theorem.
------------------------------------------------------------------------

binaryRetainedSheetCount : Nat
binaryRetainedSheetCount = 2

p3AntipodalTargetCount : Nat
p3AntipodalTargetCount = quotientOrbitCount rank1

p2RetainedAntipodalTargetCount : Nat
p2RetainedAntipodalTargetCount =
  binaryRetainedSheetCount * quotientOrbitCount rank2

p3AntipodalTargetCountIsTwo :
  p3AntipodalTargetCount ≡ 2
p3AntipodalTargetCountIsTwo = refl

p2RetainedAntipodalTargetCountIsTen :
  p2RetainedAntipodalTargetCount ≡ 10
p2RetainedAntipodalTargetCountIsTen = refl

data AntipodalTargetCountCreatesArithmeticRecognition : Set where

antipodalTargetCountDoesNotCreateArithmeticRecognition :
  AntipodalTargetCountCreatesArithmeticRecognition -> ⊥
antipodalTargetCountDoesNotCreateArithmeticRecognition ()

record BalancedTernaryAntipodal369OrbitHierarchyBoundary : Set where
  constructor balanced-ternary-antipodal-369-orbit-hierarchy-boundary
  field
    rank1ThreeToTwoConstructed : Bool
    rank2NineToFiveReused : Bool
    rank3TwentySevenToFourteenReused : Bool
    uniqueFixedCentrePlusPairsUnified : Bool
    kernelNineOrbitRechartedExactly : Bool
    p3TargetCountRecovered : Bool
    p2RetainedTargetCountRecovered : Bool
    arithmeticRecognitionAutomatic : Bool

canonicalBalancedTernaryAntipodal369OrbitHierarchyBoundary :
  BalancedTernaryAntipodal369OrbitHierarchyBoundary
canonicalBalancedTernaryAntipodal369OrbitHierarchyBoundary =
  balanced-ternary-antipodal-369-orbit-hierarchy-boundary
    true true true true true true true false
