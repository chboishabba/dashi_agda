module DASHI.Analysis.RiemannSSP15ChosenGridTransversalityExact where

------------------------------------------------------------------------
-- RH / SSP15 CHOSEN 5x3 GRID IS TRANSVERSE TO PRIME-NATIVE OBSERVERS
--
-- Existing repository facts:
--
-- * JInvariant369SSP15SignedFRACTRANBranchExact chooses an explicit bijection
--   between the 15 Ogg prime lanes and the 5 x 3 internal mode/phase carrier.
--
-- * SSP15AffineC3TranslationExact independently constructs the prime-native
--   nonary complement observer and proves its occupancies are
--
--       mode18 : 3
--       mode27 : 5
--       mode36 : 1
--       mode45 : 6
--       mode09 : 0.
--
-- Therefore the chosen 5 x 3 indexing is NOT the prime-native complement
-- partition.
--
-- This module additionally proves that each RH role-column in the chosen grid
-- crosses CM splitting classes, so the role columns are not the CM
-- split/inert/ramified partition either.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)

import DASHI.Analysis.RiemannSSP15DepthFiveRoleCodecExact as Codec
import DASHI.Analysis.RiemannSSP15SignedProvenanceBridgeExact as Provenance
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Nonary
import DASHI.Moonshine.SSP15AffineC3TranslationExact as Native
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Physics.Closure.SSP15CMFieldSplittingCorrectionReceipt as CM

------------------------------------------------------------------------
-- 1. Exact chosen role columns.
------------------------------------------------------------------------

originPrimeAt :
  Nonary.ComplementMode5 ->
  Lane.MonsterPrimeLane
originPrimeAt mode =
  Provenance.roleCodeToPrime (mode , Codec.originRole)

jPrimeAt :
  Nonary.ComplementMode5 ->
  Lane.MonsterPrimeLane
jPrimeAt mode =
  Provenance.roleCodeToPrime (mode , Codec.jRole)

sPrimeAt :
  Nonary.ComplementMode5 ->
  Lane.MonsterPrimeLane
sPrimeAt mode =
  Provenance.roleCodeToPrime (mode , Codec.sRole)

originColumn09IsP2 :
  originPrimeAt Nonary.mode09 ≡ Lane.p2
originColumn09IsP2 = refl

originColumn18IsP7 :
  originPrimeAt Nonary.mode18 ≡ Lane.p7
originColumn18IsP7 = refl

originColumn27IsP17 :
  originPrimeAt Nonary.mode27 ≡ Lane.p17
originColumn27IsP17 = refl

originColumn36IsP29 :
  originPrimeAt Nonary.mode36 ≡ Lane.p29
originColumn36IsP29 = refl

originColumn45IsP47 :
  originPrimeAt Nonary.mode45 ≡ Lane.p47
originColumn45IsP47 = refl

jColumn09IsP3 :
  jPrimeAt Nonary.mode09 ≡ Lane.p3
jColumn09IsP3 = refl

jColumn18IsP11 :
  jPrimeAt Nonary.mode18 ≡ Lane.p11
jColumn18IsP11 = refl

jColumn27IsP19 :
  jPrimeAt Nonary.mode27 ≡ Lane.p19
jColumn27IsP19 = refl

jColumn36IsP31 :
  jPrimeAt Nonary.mode36 ≡ Lane.p31
jColumn36IsP31 = refl

jColumn45IsP59 :
  jPrimeAt Nonary.mode45 ≡ Lane.p59
jColumn45IsP59 = refl

sColumn09IsP5 :
  sPrimeAt Nonary.mode09 ≡ Lane.p5
sColumn09IsP5 = refl

sColumn18IsP13 :
  sPrimeAt Nonary.mode18 ≡ Lane.p13
sColumn18IsP13 = refl

sColumn27IsP23 :
  sPrimeAt Nonary.mode27 ≡ Lane.p23
sColumn27IsP23 = refl

sColumn36IsP41 :
  sPrimeAt Nonary.mode36 ≡ Lane.p41
sColumn36IsP41 = refl

sColumn45IsP71 :
  sPrimeAt Nonary.mode45 ≡ Lane.p71
sColumn45IsP71 = refl

------------------------------------------------------------------------
-- 2. Every chosen RH role column crosses CM splitting classes.
------------------------------------------------------------------------

originColumnContainsSplit :
  Native.cmClass (originPrimeAt Nonary.mode09) ≡ CM.split
originColumnContainsSplit = refl

originColumnContainsRamified :
  Native.cmClass (originPrimeAt Nonary.mode18) ≡ CM.ramified
originColumnContainsRamified = refl

jColumnContainsInert :
  Native.cmClass (jPrimeAt Nonary.mode09) ≡ CM.inert
jColumnContainsInert = refl

jColumnContainsSplit :
  Native.cmClass (jPrimeAt Nonary.mode18) ≡ CM.split
jColumnContainsSplit = refl

sColumnContainsInert :
  Native.cmClass (sPrimeAt Nonary.mode09) ≡ CM.inert
sColumnContainsInert = refl

sColumnContainsSplit :
  Native.cmClass (sPrimeAt Nonary.mode27) ≡ CM.split
sColumnContainsSplit = refl

splitNotRamified :
  CM.split ≡ CM.ramified -> ⊥
splitNotRamified ()

inertNotSplit :
  CM.inert ≡ CM.split -> ⊥
inertNotSplit ()

originRoleColumnNotSingleCMClass :
  Native.cmClass (originPrimeAt Nonary.mode09)
  ≡ Native.cmClass (originPrimeAt Nonary.mode18)
  ->
  ⊥
originRoleColumnNotSingleCMClass same =
  splitNotRamified
    (trans (sym originColumnContainsSplit)
      (trans same originColumnContainsRamified))

jRoleColumnNotSingleCMClass :
  Native.cmClass (jPrimeAt Nonary.mode09)
  ≡ Native.cmClass (jPrimeAt Nonary.mode18)
  ->
  ⊥
jRoleColumnNotSingleCMClass same =
  inertNotSplit
    (trans (sym jColumnContainsInert)
      (trans same jColumnContainsSplit))

sRoleColumnNotSingleCMClass :
  Native.cmClass (sPrimeAt Nonary.mode09)
  ≡ Native.cmClass (sPrimeAt Nonary.mode27)
  ->
  ⊥
sRoleColumnNotSingleCMClass same =
  inertNotSplit
    (trans (sym sColumnContainsInert)
      (trans same sColumnContainsSplit))

------------------------------------------------------------------------
-- 3. Chosen internal mode is not the prime-native nonary complement observer.
--
-- The simplest witness:
--
--   chosen code (mode09, originRole) -> p2,
-- but the prime-native complement observer sends p2 -> mode27.
------------------------------------------------------------------------

mode09NotMode27 :
  Nonary.mode09 ≡ Nonary.mode27 -> ⊥
mode09NotMode27 ()

chosenMode09OriginMapsP2 :
  Provenance.roleCodeToPrime
    (Nonary.mode09 , Codec.originRole)
  ≡ Lane.p2
chosenMode09OriginMapsP2 = refl

primeNativeComplementOfChosenP2IsMode27 :
  Native.primeComplementMode
    (Provenance.roleCodeToPrime
      (Nonary.mode09 , Codec.originRole))
  ≡ Nonary.mode27
primeNativeComplementOfChosenP2IsMode27 = refl

chosenInternalModeNotPrimeNativeComplementMode :
  Native.primeComplementMode
    (Provenance.roleCodeToPrime
      (Nonary.mode09 , Codec.originRole))
  ≡ Nonary.mode09
  ->
  ⊥
chosenInternalModeNotPrimeNativeComplementMode same =
  mode09NotMode27
    (trans
      (sym same)
      primeNativeComplementOfChosenP2IsMode27)

------------------------------------------------------------------------
-- 4. Reuse the exact non-5x3 occupancy theorem.
------------------------------------------------------------------------

primeNativeComplementOccupancyTotalIsFifteen :
  Native.mode18Occupancy
  + Native.mode27Occupancy
  + Native.mode36Occupancy
  + Native.mode45Occupancy
  + Native.mode09Occupancy
  ≡ 15
primeNativeComplementOccupancyTotalIsFifteen =
  Native.primeComplementOccupanciesSumToFifteen

primeNativeMode09OccupancyIsZero :
  Native.mode09Occupancy ≡ 0
primeNativeMode09OccupancyIsZero = refl

primeNativeMode45OccupancyIsSix :
  Native.mode45Occupancy ≡ 6
primeNativeMode45OccupancyIsSix = refl

data ChosenGridIsPrimeNativeComplementPartition : Set where
data ChosenRoleColumnsAreCMClasses : Set where

chosenGridNotPromotedToPrimeNativeComplementPartition :
  ChosenGridIsPrimeNativeComplementPartition -> ⊥
chosenGridNotPromotedToPrimeNativeComplementPartition ()

chosenRoleColumnsNotPromotedToCMClasses :
  ChosenRoleColumnsAreCMClasses -> ⊥
chosenRoleColumnsNotPromotedToCMClasses ()

record RiemannSSP15ChosenGridTransversalityBoundary : Set where
  constructor riemann-ssp15-chosen-grid-transversality-boundary
  field
    exactChosenPrimeColumnsOwned : Bool
    everyRoleColumnCrossesCMClasses : Bool
    chosenInternalModeDiffersFromPrimeNativeObserver : Bool
    primeNativeOccupancyThreeFiveOneSixZeroReused : Bool
    chosenGridPromotedToPrimeNativeComplementPartition : Bool
    chosenRoleColumnsPromotedToCMPartition : Bool

canonicalRiemannSSP15ChosenGridTransversalityBoundary :
  RiemannSSP15ChosenGridTransversalityBoundary
canonicalRiemannSSP15ChosenGridTransversalityBoundary =
  riemann-ssp15-chosen-grid-transversality-boundary
    true true true true false false
