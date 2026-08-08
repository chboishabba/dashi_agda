module DASHI.Biology.StageSymmetrySSP15BridgeExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Physics.Closure.SupersingularPrimeLaneBridge as SSP
import DASHI.Physics.Closure.MonsterOggPrimeCorrectionReceipt as OggBoundary

------------------------------------------------------------------------
-- This bridge reuses the repository's established 15-lane Monster/Ogg/SSP
-- carrier.  It does not create a second prime enumeration in Foundations.
------------------------------------------------------------------------

OggPrimeLane : Set
OggPrimeLane = Lane.MonsterPrimeLane

oggPrimeLaneValue : OggPrimeLane → Nat
oggPrimeLaneValue = Lane.monsterPrimeLaneToNat

allOggPrimeLanes : List OggPrimeLane
allOggPrimeLanes = Lane.canonicalMonsterPrimeLane

allSupersingularPrimeNats : List Nat
allSupersingularPrimeNats = SSP.canonicalSupersingularPrimeLaneNats

countList : ∀ {A : Set} → List A → Nat
countList [] = 0
countList (_ ∷ xs) = 1 + countList xs

oggPrimeLaneCountIsFifteen : countList allOggPrimeLanes ≡ 15
oggPrimeLaneCountIsFifteen = refl

supersingularPrimeNatCountIsFifteen :
  countList allSupersingularPrimeNats ≡ 15
supersingularPrimeNatCountIsFifteen = refl

seventyOneIsExistingOggLane : oggPrimeLaneValue Lane.p71 ≡ 71
seventyOneIsExistingOggLane = refl

existingOggReceiptLaneCountIsFifteen :
  OggBoundary.oggPrimeCarrierLaneCount ≡ 15
existingOggReceiptLaneCountIsFifteen = refl

------------------------------------------------------------------------
-- Every lane is an observer of a retained stage carrier.  It does not replace
-- that carrier or turn arithmetic compatibility into physical Moonshine.
------------------------------------------------------------------------

data LaneStatus : Set where
  laneAffirmed laneOpen laneCountered : LaneStatus

record SymmetryLaneReading : Set where
  constructor symmetryLaneReading
  field
    primeLane : OggPrimeLane
    projectedPattern : BT.TriadPattern
    stabiliser : BT.StabiliserType
    status : LaneStatus
    residualRetained : Bool

open SymmetryLaneReading public

SSP15Signature : Set
SSP15Signature = OggPrimeLane → SymmetryLaneReading

canonicalStageFiveSSP15 : SSP15Signature
canonicalStageFiveSSP15 p =
  symmetryLaneReading
    p
    BT.twoPositiveOneOpen
    BT.pairStabiliserS2
    laneOpen
    true

------------------------------------------------------------------------
-- 81 = 10 + 71 selects the existing p71 lane arithmetically.  It does not
-- construct a 71-dimensional invariant complement or a Monster module split.
------------------------------------------------------------------------

eightyOneTenSeventyOneBridge : 10 + oggPrimeLaneValue Lane.p71 ≡ 81
eightyOneTenSeventyOneBridge = refl

record StageSymmetrySSP15Boundary : Set where
  constructor stageSymmetrySSP15Boundary
  field
    existingPrimeInfrastructureReused : Bool
    existingPrimeInfrastructureReusedIsTrue :
      existingPrimeInfrastructureReused ≡ true
    sspLaneReplacesUnderlyingCarrier : Bool
    sspLaneReplacesUnderlyingCarrierIsFalse :
      sspLaneReplacesUnderlyingCarrier ≡ false
    arithmetic71ConstructsInvariantComplement : Bool
    arithmetic71ConstructsInvariantComplementIsFalse :
      arithmetic71ConstructsInvariantComplement ≡ false
    physicalMoonshinePromoted : Bool
    physicalMoonshinePromotedIsFalse : physicalMoonshinePromoted ≡ false

canonicalStageSymmetrySSP15Boundary : StageSymmetrySSP15Boundary
canonicalStageSymmetrySSP15Boundary =
  stageSymmetrySSP15Boundary true refl false refl false refl false refl
