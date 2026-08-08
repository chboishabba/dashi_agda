module DASHI.Biology.StageSymmetrySSP15BridgeExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Physics.Closure.SupersingularPrimeLaneBridge as SSP
import DASHI.Physics.Closure.MonsterOggPrimeCorrectionReceipt as OggBoundary
import DASHI.Biology.OggPrimeNonaryAddressExact as Address
import DASHI.Biology.SSP15NineObserverAtlasExact as Atlas

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

-- Backwards-compatible stage-only observer.  It intentionally forgets the
-- prime-specific nonary address and observer kind supplied below.
canonicalStageFiveSSP15 : SSP15Signature
canonicalStageFiveSSP15 p =
  symmetryLaneReading
    p
    BT.twoPositiveOneOpen
    BT.pairStabiliserS2
    laneOpen
    true

record PrimeSpecificSymmetryLaneReading
    (prime : OggPrimeLane) : Set where
  constructor prime-specific-symmetry-lane-reading
  field
    stageReading : SymmetryLaneReading
    stageReadingUsesPrime : primeLane stageReading ≡ prime
    nonaryAddress : Address.NonaryOggAddress prime
    nineObserver : Atlas.SSP15NineAtlasEntry prime

open PrimeSpecificSymmetryLaneReading public

canonicalPrimeSpecificSSP15 :
  (prime : OggPrimeLane) → PrimeSpecificSymmetryLaneReading prime
canonicalPrimeSpecificSSP15 prime =
  prime-specific-symmetry-lane-reading
    (canonicalStageFiveSSP15 prime)
    refl
    (Address.nonaryOggAddress prime)
    (Atlas.ssp15NineAtlas prime)

primeSpecificAddressReconstructsLane :
  (prime : OggPrimeLane) →
  oggPrimeLaneValue prime
  ≡ Address.coarseSheets
      (nonaryAddress (canonicalPrimeSpecificSSP15 prime)) * 9
    + Address.remainder
      (nonaryAddress (canonicalPrimeSpecificSSP15 prime))
primeSpecificAddressReconstructsLane prime =
  Address.addressExact
    (nonaryAddress (canonicalPrimeSpecificSSP15 prime))

primeSpecificObserverMatchesLane :
  (prime : OggPrimeLane) →
  Atlas.observedValue
    (nineObserver (canonicalPrimeSpecificSSP15 prime))
  ≡ oggPrimeLaneValue prime
primeSpecificObserverMatchesLane prime =
  Atlas.observedValueIsPrimeLane
    (nineObserver (canonicalPrimeSpecificSSP15 prime))

p71PrimeSpecificCoarseDepth :
  Address.coarseSheets
    (nonaryAddress (canonicalPrimeSpecificSSP15 Lane.p71)) ≡ 7
p71PrimeSpecificCoarseDepth = refl

p71PrimeSpecificRemainder :
  Address.remainder
    (nonaryAddress (canonicalPrimeSpecificSSP15 Lane.p71)) ≡ 8
p71PrimeSpecificRemainder = refl

eightyOneTenSeventyOneBridge : 10 + oggPrimeLaneValue Lane.p71 ≡ 81
eightyOneTenSeventyOneBridge = refl

record StageSymmetrySSP15Boundary : Set₁ where
  constructor stageSymmetrySSP15Boundary
  field
    oggLaneCountWitness : countList allOggPrimeLanes ≡ 15
    supersingularNatCountWitness : countList allSupersingularPrimeNats ≡ 15
    existingReceiptCountWitness :
      OggBoundary.oggPrimeCarrierLaneCount ≡ 15
    everyPrimeSpecificAddressReconstructs :
      (prime : OggPrimeLane) →
      oggPrimeLaneValue prime
      ≡ Address.coarseSheets
          (nonaryAddress (canonicalPrimeSpecificSSP15 prime)) * 9
        + Address.remainder
          (nonaryAddress (canonicalPrimeSpecificSSP15 prime))
    everyPrimeSpecificObserverMatches :
      (prime : OggPrimeLane) →
      Atlas.observedValue
        (nineObserver (canonicalPrimeSpecificSSP15 prime))
      ≡ oggPrimeLaneValue prime
    legacyUniformReadingContainsPrimeSpecificAddress : Bool
    legacyUniformReadingContainsPrimeSpecificAddressIsFalse :
      legacyUniformReadingContainsPrimeSpecificAddress ≡ false
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
  stageSymmetrySSP15Boundary
    oggPrimeLaneCountIsFifteen
    supersingularPrimeNatCountIsFifteen
    existingOggReceiptLaneCountIsFifteen
    primeSpecificAddressReconstructsLane
    primeSpecificObserverMatchesLane
    false refl
    false refl
    false refl
    false refl
