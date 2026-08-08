module DASHI.Foundations.DialecticCubieTetralemmaExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.DialecticSheetFrameSelectorExact as Sheet

data SupportBit : Set where
  unsupported supported : SupportBit

record SupportCounterSquare : Set where
  constructor supportCounterSquare
  field
    support counterSupport : SupportBit

open SupportCounterSquare public

data TetralemmaPosition : Set where
  positionOnly counterpositionOnly bothSupported neitherEstablished :
    TetralemmaPosition

classifySupportSquare : SupportCounterSquare → TetralemmaPosition
classifySupportSquare (supportCounterSquare supported unsupported) = positionOnly
classifySupportSquare (supportCounterSquare unsupported supported) = counterpositionOnly
classifySupportSquare (supportCounterSquare supported supported) = bothSupported
classifySupportSquare (supportCounterSquare unsupported unsupported) = neitherEstablished

record TetralemmaOver (Carrier : Set) : Set where
  constructor tetralemmaOver
  field
    retainedCarrier : Carrier
    supportSquare : SupportCounterSquare
    position : TetralemmaPosition
    positionExact : position ≡ classifySupportSquare supportSquare

open TetralemmaOver public

stageThreePatternWithCounterSquare : TetralemmaOver BT.TriadPattern
stageThreePatternWithCounterSquare =
  tetralemmaOver
    BT.allPositive
    (supportCounterSquare supported supported)
    bothSupported refl

stageThreeCarrierRetained :
  retainedCarrier stageThreePatternWithCounterSquare ≡ BT.allPositive
stageThreeCarrierRetained = refl

supportSquareCardinality : Nat
supportSquareCardinality = 2 * 2

supportSquareCardinalityIsFour : supportSquareCardinality ≡ 4
supportSquareCardinalityIsFour = refl

data Axis3 : Set where
  low middle high : Axis3

axis3Cardinality : Nat
axis3Cardinality = 3

cubiePositionCardinality : Nat
cubiePositionCardinality =
  axis3Cardinality * axis3Cardinality * axis3Cardinality

cubiePositionCardinalityIsTwentySeven :
  cubiePositionCardinality ≡ 27
cubiePositionCardinalityIsTwentySeven = refl

record CubiePosition : Set where
  constructor cubiePosition
  field
    row column context : Axis3

TernaryCubieField : Set
TernaryCubieField = CubiePosition → BT.BalancedDigit

constantOpenCubie : TernaryCubieField
constantOpenCubie position = BT.zeroDigit

contextSlice : TernaryCubieField → Axis3 → Axis3 → Axis3 → BT.BalancedDigit
contextSlice cubie context row column =
  cubie (cubiePosition row column context)

sheetEntry : Sheet.ComparisonSheet3x3 → Axis3 → Axis3 → BT.BalancedDigit
sheetEntry sheet low low = Sheet.c11 sheet
sheetEntry sheet low middle = Sheet.c12 sheet
sheetEntry sheet low high = Sheet.c13 sheet
sheetEntry sheet middle low = Sheet.c21 sheet
sheetEntry sheet middle middle = Sheet.c22 sheet
sheetEntry sheet middle high = Sheet.c23 sheet
sheetEntry sheet high low = Sheet.c31 sheet
sheetEntry sheet high middle = Sheet.c32 sheet
sheetEntry sheet high high = Sheet.c33 sheet

repeatSheetAcrossContext : Sheet.ComparisonSheet3x3 → TernaryCubieField
repeatSheetAcrossContext sheet (cubiePosition row column context) =
  sheetEntry sheet row column

repeatedSheetIgnoresContext :
  (sheet : Sheet.ComparisonSheet3x3)
  (row column leftContext rightContext : Axis3) →
  repeatSheetAcrossContext sheet
    (cubiePosition row column leftContext)
  ≡
  repeatSheetAcrossContext sheet
    (cubiePosition row column rightContext)
repeatedSheetIgnoresContext sheet row column leftContext rightContext = refl

positiveOnlyDecision : BT.BalancedDigit → Sheet.Bit2
positiveOnlyDecision BT.neg = Sheet.bit0
positiveOnlyDecision BT.zeroDigit = Sheet.bit0
positiveOnlyDecision BT.pos = Sheet.bit1

nonzeroDecision : BT.BalancedDigit → Sheet.Bit2
nonzeroDecision BT.neg = Sheet.bit1
nonzeroDecision BT.zeroDigit = Sheet.bit0
nonzeroDecision BT.pos = Sheet.bit1

positiveOnlyRejectsNegative : positiveOnlyDecision BT.neg ≡ Sheet.bit0
positiveOnlyRejectsNegative = refl

nonzeroAcceptsNegative : nonzeroDecision BT.neg ≡ Sheet.bit1
nonzeroAcceptsNegative = refl

decisionPoliciesDifferOnNegative :
  positiveOnlyDecision BT.neg ≡ nonzeroDecision BT.neg → ⊥
decisionPoliciesDifferOnNegative ()

data PolicyName : Set where
  positiveOnlyName nonzeroName : PolicyName

record DeclaredDecisionPolicy : Set where
  constructor declaredDecisionPolicy
  field
    decide : BT.BalancedDigit → Sheet.Bit2
    policyName : PolicyName

positiveOnlyPolicy : DeclaredDecisionPolicy
positiveOnlyPolicy =
  declaredDecisionPolicy positiveOnlyDecision positiveOnlyName

nonzeroPolicy : DeclaredDecisionPolicy
nonzeroPolicy = declaredDecisionPolicy nonzeroDecision nonzeroName

policyNamesDiffer : positiveOnlyName ≡ nonzeroName → ⊥
policyNamesDiffer ()

record Hyperfabric (Cell : Set) : Set₁ where
  constructor hyperfabric
  field
    cells : List Cell
    incident : Cell → Cell → Set
    gluingWitnessSupplied : Bool

open Hyperfabric public

data CubieFrameName : Set where
  localCubieFrame contextualCubieFrame promotedCubieFrame : CubieFrameName

record CubieWithFrame : Set where
  constructor cubieWithFrame
  field
    cubieField : TernaryCubieField
    frameName : CubieFrameName

emptyCubieHyperfabric : Hyperfabric CubieWithFrame
emptyCubieHyperfabric =
  hyperfabric [] (λ left right → ⊥) false

record DialecticCubieBoundary : Set where
  constructor dialecticCubieBoundary
  field
    twentySevenPositionsIdentifiedWithTwentySevenStates : Bool
    twentySevenPositionsIdentifiedWithTwentySevenStatesIsFalse :
      twentySevenPositionsIdentifiedWithTwentySevenStates ≡ false
    tetralemmaErasesPriorCarrier : Bool
    tetralemmaErasesPriorCarrierIsFalse :
      tetralemmaErasesPriorCarrier ≡ false
    binaryDecisionPolicyCanonicalWithoutDeclaration : Bool
    binaryDecisionPolicyCanonicalWithoutDeclarationIsFalse :
      binaryDecisionPolicyCanonicalWithoutDeclaration ≡ false
    cubieListAloneProvesManifold : Bool
    cubieListAloneProvesManifoldIsFalse :
      cubieListAloneProvesManifold ≡ false

canonicalDialecticCubieBoundary : DialecticCubieBoundary
canonicalDialecticCubieBoundary =
  dialecticCubieBoundary false refl false refl false refl false refl
