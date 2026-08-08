module DASHI.Foundations.StageSymmetryCarrierTowerExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT

------------------------------------------------------------------------
-- The stage numerals are projections of finite symmetry carriers.  Carrier
-- cardinality, group action, constituent decomposition, and amplitude are kept
-- separate.
------------------------------------------------------------------------

data C2 : Set where
  direct inverse : C2

flipC2 : C2 → C2
flipC2 direct = inverse
flipC2 inverse = direct

flipC2Involutive : (x : C2) → flipC2 (flipC2 x) ≡ x
flipC2Involutive direct = refl
flipC2Involutive inverse = refl

data C3 : Set where
  negative neutral positive : C3

rotateC3 : C3 → C3
rotateC3 negative = neutral
rotateC3 neutral = positive
rotateC3 positive = negative

rotateC3OrderThree :
  (x : C3) → rotateC3 (rotateC3 (rotateC3 x)) ≡ x
rotateC3OrderThree negative = refl
rotateC3OrderThree neutral = refl
rotateC3OrderThree positive = refl

record SquareCarrier : Set where
  constructor squareCarrier
  field
    horizontal vertical : C2

record HexadicCarrier : Set where
  constructor hexadicCarrier
  field
    ternaryContent : C3
    binaryOrientation : C2

record NonaryCarrier : Set where
  constructor nonaryCarrier
  field
    row column : C3

------------------------------------------------------------------------
-- Cardinality ledger, backed by explicit complete finite enumerations.
------------------------------------------------------------------------

c2Cardinality : Nat
c2Cardinality = 2

c3Cardinality : Nat
c3Cardinality = 3

squareCardinality : Nat
squareCardinality = c2Cardinality * c2Cardinality

hexadicCardinality : Nat
hexadicCardinality = c2Cardinality * c3Cardinality

nonaryCardinality : Nat
nonaryCardinality = c3Cardinality * c3Cardinality

squareCardinalityIsFour : squareCardinality ≡ 4
squareCardinalityIsFour = refl

hexadicCardinalityIsSix : hexadicCardinality ≡ 6
hexadicCardinalityIsSix = refl

nonaryCardinalityIsNine : nonaryCardinality ≡ 9
nonaryCardinalityIsNine = refl

carrierListLength : ∀ {A : Set} → List A → Nat
carrierListLength [] = 0
carrierListLength (_ ∷ xs) = 1 + carrierListLength xs

allSquareCarriers : List SquareCarrier
allSquareCarriers =
  squareCarrier direct direct
  ∷ squareCarrier direct inverse
  ∷ squareCarrier inverse direct
  ∷ squareCarrier inverse inverse
  ∷ []

allHexadicCarriers : List HexadicCarrier
allHexadicCarriers =
  hexadicCarrier negative direct
  ∷ hexadicCarrier negative inverse
  ∷ hexadicCarrier neutral direct
  ∷ hexadicCarrier neutral inverse
  ∷ hexadicCarrier positive direct
  ∷ hexadicCarrier positive inverse
  ∷ []

allNonaryCarriers : List NonaryCarrier
allNonaryCarriers =
  nonaryCarrier negative negative
  ∷ nonaryCarrier negative neutral
  ∷ nonaryCarrier negative positive
  ∷ nonaryCarrier neutral negative
  ∷ nonaryCarrier neutral neutral
  ∷ nonaryCarrier neutral positive
  ∷ nonaryCarrier positive negative
  ∷ nonaryCarrier positive neutral
  ∷ nonaryCarrier positive positive
  ∷ []

squareEnumerationMatchesCardinality :
  carrierListLength allSquareCarriers ≡ squareCardinality
squareEnumerationMatchesCardinality = refl

hexadicEnumerationMatchesCardinality :
  carrierListLength allHexadicCarriers ≡ hexadicCardinality
hexadicEnumerationMatchesCardinality = refl

nonaryEnumerationMatchesCardinality :
  carrierListLength allNonaryCarriers ≡ nonaryCardinality
nonaryEnumerationMatchesCardinality = refl

fiveIsClosedTriadPlusOpenPair : c3Cardinality + c2Cardinality ≡ 5
fiveIsClosedTriadPlusOpenPair = refl

sixIsPairTimesTriad : c2Cardinality * c3Cardinality ≡ 6
sixIsPairTimesTriad = refl

sixIsNonaryMinusTriad : 6 + c3Cardinality ≡ nonaryCardinality
sixIsNonaryMinusTriad = refl

------------------------------------------------------------------------
-- Symmetry order zero means no installed active distinction.  Its carrier is
-- one root point with a trivial automorphism, not a zero-cardinality set.
------------------------------------------------------------------------

data RootCarrier : Set where
  rootPoint : RootCarrier

data TrivialAutomorphism : Set where
  identityOnly : TrivialAutomorphism

record SymmetryLevel : Set where
  constructor symmetryLevel
  field
    activeDistinctionCount : Nat
    carrierCardinality : Nat
    descriptionCode : Nat

rootSymmetryLevel : SymmetryLevel
rootSymmetryLevel = symmetryLevel 0 1 0

firstPairSymmetryLevel : SymmetryLevel
firstPairSymmetryLevel = symmetryLevel 1 2 1

squareSymmetryLevel : SymmetryLevel
squareSymmetryLevel = symmetryLevel 2 4 2

triadicSymmetryLevel : SymmetryLevel
triadicSymmetryLevel = symmetryLevel 1 3 3

hexadicSymmetryLevel : SymmetryLevel
hexadicSymmetryLevel = symmetryLevel 2 6 6

nonarySymmetryLevel : SymmetryLevel
nonarySymmetryLevel = symmetryLevel 2 9 9

------------------------------------------------------------------------
-- The Stage-5 constituent is a symmetry mismatch: a full S3-stabilised triad
-- joined to an S2-stabilised open triad.  Completion restores S3 on the second
-- constituent; fallback retains the S2 fibre.
------------------------------------------------------------------------

record StageFiveSymmetryMismatch : Set where
  constructor stageFiveSymmetryMismatch
  field
    closedConstituent : BT.SymmetryAwareStageState
    openConstituent : BT.SymmetryAwareStageState
    totalAmplitude : Nat
    totalAmplitudeIsFive : totalAmplitude ≡ 5
    totalAmplitudeFromConstituents :
      BT.positiveUnits
        (BT.SymmetryAwareStageState.balance closedConstituent)
      + BT.positiveUnits
          (BT.SymmetryAwareStageState.balance openConstituent)
      ≡ totalAmplitude
    closedStabiliserIsS3 :
      BT.SymmetryAwareStageState.stabiliser closedConstituent
      ≡ BT.fullStabiliserS3
    openStabiliserIsS2 :
      BT.SymmetryAwareStageState.stabiliser openConstituent
      ≡ BT.pairStabiliserS2

canonicalStageFiveSymmetryMismatch : StageFiveSymmetryMismatch
canonicalStageFiveSymmetryMismatch =
  stageFiveSymmetryMismatch
    BT.stage3SymmetryState
    BT.stage2SymmetryState
    5 refl refl refl refl

record SymmetryTowerBoundary : Set where
  constructor symmetryTowerBoundary
  field
    equalCardinalityImpliesSameAction : Bool
    equalCardinalityImpliesSameActionIsFalse :
      equalCardinalityImpliesSameAction ≡ false
    amplitudeDeterminesPattern : Bool
    amplitudeDeterminesPatternIsFalse : amplitudeDeterminesPattern ≡ false
    counterpositionAlwaysInverse : Bool
    counterpositionAlwaysInverseIsFalse : counterpositionAlwaysInverse ≡ false

canonicalSymmetryTowerBoundary : SymmetryTowerBoundary
canonicalSymmetryTowerBoundary =
  symmetryTowerBoundary false refl false refl false refl
