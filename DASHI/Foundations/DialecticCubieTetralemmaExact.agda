module DASHI.Foundations.DialecticCubieTetralemmaExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.DialecticSheetFrameSelectorExact as Sheet

------------------------------------------------------------------------
-- A tetralemma is a two-axis support/counter-support square over an existing
-- carrier.  The four does not erase or replace the carrier being classified.
------------------------------------------------------------------------

data SupportBit : Set where
  unsupported supported : SupportBit

record SupportCounterSquare : Set where
  constructor supportCounterSquare
  field
    support counterSupport : SupportBit

open SupportCounterSquare public

data TetralemmaPosition : Set where
  positionOnly : TetralemmaPosition
  counterpositionOnly : TetralemmaPosition
  bothSupported : TetralemmaPosition
  neitherEstablished : TetralemmaPosition

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
    bothSupported
    refl

stageThreeCarrierRetained :
  retainedCarrier stageThreePatternWithCounterSquare ≡ BT.allPositive
stageThreeCarrierRetained = refl

supportSquareCardinality : Nat
supportSquareCardinality = 2 * 2

supportSquareCardinalityIsFour : supportSquareCardinality ≡ 4
supportSquareCardinalityIsFour = refl

------------------------------------------------------------------------
-- The 3x3 comparison sheet and a third context axis generate 27 positions.
-- A cubie field assigns one balanced ternary value to each position.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- A concrete lift of the nine-cell sheet to a cubie repeats the relational
-- sheet across three declared contexts.  More informative context actions can
-- be supplied later without changing the carrier.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Ternary observation may be reduced to a binary commitment, but the quotient
-- policy must be explicit.  Positive-only and nonzero policies differ on a
-- negative observation.
------------------------------------------------------------------------

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

record DeclaredDecisionPolicy : Set where
  constructor declaredDecisionPolicy
  field
    decide : BT.BalancedDigit → Sheet.Bit2
    policyNameCode : Nat

positiveOnlyPolicy : DeclaredDecisionPolicy
positiveOnlyPolicy = declaredDecisionPolicy positiveOnlyDecision 1

nonzeroPolicy : DeclaredDecisionPolicy
nonzeroPolicy = declaredDecisionPolicy nonzeroDecision 2

------------------------------------------------------------------------
-- Hyperfabrics retain cubies and an explicit incidence relation.  The record
-- supplies the construction obligation without pretending every list of cubies
-- is already a manifold, braid, or sheaf.
------------------------------------------------------------------------

record Hyperfabric (Cell : Set) : Set₁ where
  constructor hyperfabric
  field
    cells : List Cell
    incident : Cell → Cell → Set
    gluingWitnessSupplied : Bool

open Hyperfabric public

record CubieWithFrame : Set where
  constructor cubieWithFrame
  field
    field : TernaryCubieField
    frameCode : Nat

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
