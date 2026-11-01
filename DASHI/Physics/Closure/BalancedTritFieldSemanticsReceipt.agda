module DASHI.Physics.Closure.BalancedTritFieldSemanticsReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Algebra.Trit as Trit
import DASHI.Physics.RealTernaryCarrier as RTC
import DASHI.Physics.TritCarrierBridge as Bridge

------------------------------------------------------------------------
-- Balanced-trit field semantics receipt.
--
-- This receipt fixes the notation boundary requested by Manager A.  Decimal
-- forms are recorded as notation/readout only: the carrier remains the
-- balanced trit field neg/zer/pos over RealTernaryCarrier.  In particular,
-- "10" names a supervoxel population readout, and "0.1" names a subvoxel
-- pull readout; neither changes the carrier base to base 10.

data BalancedTritFieldSemanticsStatus : Set where
  balancedTritCarrier_decimalNotationBoundaryRecorded :
    BalancedTritFieldSemanticsStatus

data BalancedTritSemanticPiece : Set where
  balancedTritFieldNegZeroPos :
    BalancedTritSemanticPiece

  realTernaryCarrierVecTrit :
    BalancedTritSemanticPiece

  tritCarrierBridgeTriTruthEquivalence :
    BalancedTritSemanticPiece

  decimalNotationOnly :
    BalancedTritSemanticPiece

  tenSupervoxelPopulationReadout :
    BalancedTritSemanticPiece

  zeroPointOneSubvoxelPullReadout :
    BalancedTritSemanticPiece

  plusTwoPlusThreeAccumulationSublation :
    BalancedTritSemanticPiece

  balancedTernaryCarryRollover :
    BalancedTritSemanticPiece

  fractranValuationStepReadout :
    BalancedTritSemanticPiece

  noRuntimeCodecClaim :
    BalancedTritSemanticPiece

  noBaseTenCarrierPromotion :
    BalancedTritSemanticPiece

canonicalBalancedTritSemanticPieces :
  List BalancedTritSemanticPiece
canonicalBalancedTritSemanticPieces =
  balancedTritFieldNegZeroPos
  ∷ realTernaryCarrierVecTrit
  ∷ tritCarrierBridgeTriTruthEquivalence
  ∷ decimalNotationOnly
  ∷ tenSupervoxelPopulationReadout
  ∷ zeroPointOneSubvoxelPullReadout
  ∷ plusTwoPlusThreeAccumulationSublation
  ∷ balancedTernaryCarryRollover
  ∷ fractranValuationStepReadout
  ∷ noRuntimeCodecClaim
  ∷ noBaseTenCarrierPromotion
  ∷ []

data DecimalNotationRole : Set where
  notationOnly_notCarrierBase :
    DecimalNotationRole

data SupervoxelDecimalReadout : Set where
  tenAsSupervoxelPopulation :
    SupervoxelDecimalReadout

data SubvoxelDecimalReadout : Set where
  zeroPointOneAsSubvoxelPull :
    SubvoxelDecimalReadout

data AccumulationSublationReadout : Set where
  plusTwoPlusThreeAccumulatedAndSublated :
    AccumulationSublationReadout

data CarryRolloverReadout : Set where
  tenToElevenAsBalancedTernaryCarry :
    CarryRolloverReadout

data FractranValuationReadout : Set where
  fractranValuationStepNotationOnly :
    FractranValuationReadout

data BalancedTritFieldPromotion : Set where

balancedTritFieldPromotionImpossibleHere :
  BalancedTritFieldPromotion →
  ⊥
balancedTritFieldPromotionImpossibleHere ()

decimalNotationStatement : String
decimalNotationStatement =
  "Decimal glyphs are notation/readout only; the carrier base is balanced ternary over Trit neg/zer/pos."

tenSupervoxelStatement : String
tenSupervoxelStatement =
  "10 is read as a supervoxel population notation, not as evidence that the carrier base is decimal."

zeroPointOneSubvoxelStatement : String
zeroPointOneSubvoxelStatement =
  "0.1 is read as a subvoxel pull notation, represented by the scaled pair 1/10 only at the notation boundary."

accumulationSublationStatement : String
accumulationSublationStatement =
  "+2 and +3 are recorded as accumulation/sublation readouts over balanced trit semantics, not as decimal-base carrier digits."

carryRolloverStatement : String
carryRolloverStatement =
  "10 -> 11 is a balanced-ternary carry/rollover notation: one supervoxel population is carried into the next valuation readout while preserving the trit carrier."

fractranValuationStatement : String
fractranValuationStatement =
  "The carry/rollover may be read as a FRACTRAN valuation step at the notation boundary only; this receipt does not construct or claim a runtime codec."

balancedTritFieldSemanticsStatement : String
balancedTritFieldSemanticsStatement =
  "Balanced trit field semantics are carried by RealTernaryCarrier and TritCarrierBridge; decimal 10, decimal 0.1, 10 -> 11 carry/rollover, and +2/+3 accumulation/sublation are notation-layer readouts only."

record BalancedTritFieldSemanticsReceipt : Setω where
  field
    status :
      BalancedTritFieldSemanticsStatus

    statusIsCanonical :
      status
      ≡
      balancedTritCarrier_decimalNotationBoundaryRecorded

    tritNegative :
      Trit.Trit

    tritNegativeIsCanonical :
      tritNegative ≡ Trit.neg

    tritZero :
      Trit.Trit

    tritZeroIsCanonical :
      tritZero ≡ Trit.zer

    tritPositive :
      Trit.Trit

    tritPositiveIsCanonical :
      tritPositive ≡ Trit.pos

    sampleCarrierLength :
      Nat

    sampleCarrierLengthIsThree :
      sampleCarrierLength ≡ 3

    sampleCarrier :
      Set

    sampleCarrierIsRealTernaryCarrier :
      sampleCarrier ≡ RTC.Carrier sampleCarrierLength

    tritBridge :
      Bridge.TritCarrierBridge sampleCarrierLength

    tritBridgeIsCanonical :
      tritBridge ≡ Bridge.tritCarrierBridgeSurface sampleCarrierLength

    decimalNotationRole :
      DecimalNotationRole

    decimalNotationRoleIsNotationOnly :
      decimalNotationRole ≡ notationOnly_notCarrierBase

    decimalNotationBoundary :
      String

    decimalNotationBoundaryIsCanonical :
      decimalNotationBoundary ≡ decimalNotationStatement

    tenReadout :
      SupervoxelDecimalReadout

    tenReadoutIsSupervoxelPopulation :
      tenReadout ≡ tenAsSupervoxelPopulation

    tenNotation :
      String

    tenNotationIsCanonical :
      tenNotation ≡ "10"

    tenSupervoxelPopulation :
      Nat

    tenSupervoxelPopulationIsTen :
      tenSupervoxelPopulation ≡ 10

    tenStatement :
      String

    tenStatementIsCanonical :
      tenStatement ≡ tenSupervoxelStatement

    zeroPointOneReadout :
      SubvoxelDecimalReadout

    zeroPointOneReadoutIsSubvoxelPull :
      zeroPointOneReadout ≡ zeroPointOneAsSubvoxelPull

    zeroPointOneNotation :
      String

    zeroPointOneNotationIsCanonical :
      zeroPointOneNotation ≡ "0.1"

    subvoxelPullNumerator :
      Nat

    subvoxelPullNumeratorIsOne :
      subvoxelPullNumerator ≡ 1

    subvoxelPullDenominator :
      Nat

    subvoxelPullDenominatorIsTen :
      subvoxelPullDenominator ≡ 10

    zeroPointOneStatement :
      String

    zeroPointOneStatementIsCanonical :
      zeroPointOneStatement ≡ zeroPointOneSubvoxelStatement

    plusTwo :
      Nat

    plusTwoIsTwo :
      plusTwo ≡ 2

    plusThree :
      Nat

    plusThreeIsThree :
      plusThree ≡ 3

    accumulationSublationReadout :
      AccumulationSublationReadout

    accumulationSublationReadoutIsCanonical :
      accumulationSublationReadout
      ≡
      plusTwoPlusThreeAccumulatedAndSublated

    accumulationSublationStatementField :
      String

    accumulationSublationStatementIsCanonical :
      accumulationSublationStatementField ≡ accumulationSublationStatement

    carryRolloverReadout :
      CarryRolloverReadout

    carryRolloverReadoutIsCanonical :
      carryRolloverReadout ≡ tenToElevenAsBalancedTernaryCarry

    carryRolloverFromNotation :
      String

    carryRolloverFromNotationIsTen :
      carryRolloverFromNotation ≡ "10"

    carryRolloverToNotation :
      String

    carryRolloverToNotationIsEleven :
      carryRolloverToNotation ≡ "11"

    carryRolloverStatementField :
      String

    carryRolloverStatementIsCanonical :
      carryRolloverStatementField ≡ carryRolloverStatement

    fractranValuationReadout :
      FractranValuationReadout

    fractranValuationReadoutIsNotationOnly :
      fractranValuationReadout ≡ fractranValuationStepNotationOnly

    fractranValuationStepRecorded :
      Bool

    fractranValuationStepRecordedIsTrue :
      fractranValuationStepRecorded ≡ true

    fractranValuationStatementField :
      String

    fractranValuationStatementIsCanonical :
      fractranValuationStatementField ≡ fractranValuationStatement

    runtimeCodecClaimed :
      Bool

    runtimeCodecClaimedIsFalse :
      runtimeCodecClaimed ≡ false

    decimalCarrierBasePromoted :
      Bool

    decimalCarrierBasePromotedIsFalse :
      decimalCarrierBasePromoted ≡ false

    baseTenCarrierClaimed :
      Bool

    baseTenCarrierClaimedIsFalse :
      baseTenCarrierClaimed ≡ false

    decimalArithmeticSemanticsClaimed :
      Bool

    decimalArithmeticSemanticsClaimedIsFalse :
      decimalArithmeticSemanticsClaimed ≡ false

    balancedTritCarrierPreserved :
      Bool

    balancedTritCarrierPreservedIsTrue :
      balancedTritCarrierPreserved ≡ true

    semanticPieces :
      List BalancedTritSemanticPiece

    semanticPiecesAreCanonical :
      semanticPieces ≡ canonicalBalancedTritSemanticPieces

    promotionFlags :
      List BalancedTritFieldPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ balancedTritFieldSemanticsStatement

    receiptBoundary :
      List String

open BalancedTritFieldSemanticsReceipt public

canonicalBalancedTritFieldSemanticsReceipt :
  BalancedTritFieldSemanticsReceipt
canonicalBalancedTritFieldSemanticsReceipt =
  record
    { status =
        balancedTritCarrier_decimalNotationBoundaryRecorded
    ; statusIsCanonical =
        refl
    ; tritNegative =
        Trit.neg
    ; tritNegativeIsCanonical =
        refl
    ; tritZero =
        Trit.zer
    ; tritZeroIsCanonical =
        refl
    ; tritPositive =
        Trit.pos
    ; tritPositiveIsCanonical =
        refl
    ; sampleCarrierLength =
        3
    ; sampleCarrierLengthIsThree =
        refl
    ; sampleCarrier =
        RTC.Carrier 3
    ; sampleCarrierIsRealTernaryCarrier =
        refl
    ; tritBridge =
        Bridge.tritCarrierBridgeSurface 3
    ; tritBridgeIsCanonical =
        refl
    ; decimalNotationRole =
        notationOnly_notCarrierBase
    ; decimalNotationRoleIsNotationOnly =
        refl
    ; decimalNotationBoundary =
        decimalNotationStatement
    ; decimalNotationBoundaryIsCanonical =
        refl
    ; tenReadout =
        tenAsSupervoxelPopulation
    ; tenReadoutIsSupervoxelPopulation =
        refl
    ; tenNotation =
        "10"
    ; tenNotationIsCanonical =
        refl
    ; tenSupervoxelPopulation =
        10
    ; tenSupervoxelPopulationIsTen =
        refl
    ; tenStatement =
        tenSupervoxelStatement
    ; tenStatementIsCanonical =
        refl
    ; zeroPointOneReadout =
        zeroPointOneAsSubvoxelPull
    ; zeroPointOneReadoutIsSubvoxelPull =
        refl
    ; zeroPointOneNotation =
        "0.1"
    ; zeroPointOneNotationIsCanonical =
        refl
    ; subvoxelPullNumerator =
        1
    ; subvoxelPullNumeratorIsOne =
        refl
    ; subvoxelPullDenominator =
        10
    ; subvoxelPullDenominatorIsTen =
        refl
    ; zeroPointOneStatement =
        zeroPointOneSubvoxelStatement
    ; zeroPointOneStatementIsCanonical =
        refl
    ; plusTwo =
        2
    ; plusTwoIsTwo =
        refl
    ; plusThree =
        3
    ; plusThreeIsThree =
        refl
    ; accumulationSublationReadout =
        plusTwoPlusThreeAccumulatedAndSublated
    ; accumulationSublationReadoutIsCanonical =
        refl
    ; accumulationSublationStatementField =
        accumulationSublationStatement
    ; accumulationSublationStatementIsCanonical =
        refl
    ; carryRolloverReadout =
        tenToElevenAsBalancedTernaryCarry
    ; carryRolloverReadoutIsCanonical =
        refl
    ; carryRolloverFromNotation =
        "10"
    ; carryRolloverFromNotationIsTen =
        refl
    ; carryRolloverToNotation =
        "11"
    ; carryRolloverToNotationIsEleven =
        refl
    ; carryRolloverStatementField =
        carryRolloverStatement
    ; carryRolloverStatementIsCanonical =
        refl
    ; fractranValuationReadout =
        fractranValuationStepNotationOnly
    ; fractranValuationReadoutIsNotationOnly =
        refl
    ; fractranValuationStepRecorded =
        true
    ; fractranValuationStepRecordedIsTrue =
        refl
    ; fractranValuationStatementField =
        fractranValuationStatement
    ; fractranValuationStatementIsCanonical =
        refl
    ; runtimeCodecClaimed =
        false
    ; runtimeCodecClaimedIsFalse =
        refl
    ; decimalCarrierBasePromoted =
        false
    ; decimalCarrierBasePromotedIsFalse =
        refl
    ; baseTenCarrierClaimed =
        false
    ; baseTenCarrierClaimedIsFalse =
        refl
    ; decimalArithmeticSemanticsClaimed =
        false
    ; decimalArithmeticSemanticsClaimedIsFalse =
        refl
    ; balancedTritCarrierPreserved =
        true
    ; balancedTritCarrierPreservedIsTrue =
        refl
    ; semanticPieces =
        canonicalBalancedTritSemanticPieces
    ; semanticPiecesAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        balancedTritFieldSemanticsStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "RealTernaryCarrier.Carrier n is Vec Trit n with Trit neg/zer/pos"
        ∷ "TritCarrierBridge records the TriTruth equivalence and rotation/reflection isometries"
        ∷ "Decimal 10 is only a supervoxel population readout"
        ∷ "Decimal 0.1 is only a subvoxel pull readout represented by notation pair 1/10"
        ∷ "The 10 -> 11 rollover is balanced-ternary carry notation and a FRACTRAN valuation-step readout only"
        ∷ "+2 and +3 are accumulation/sublation readouts over the balanced trit semantics"
        ∷ "No runtime codec is claimed or constructed"
        ∷ "No field promotes decimal arithmetic or base-10 carrier semantics"
        ∷ []
    }

balancedTritFieldSemanticsKeepsBaseTenFalse :
  baseTenCarrierClaimed canonicalBalancedTritFieldSemanticsReceipt
  ≡ false
balancedTritFieldSemanticsKeepsBaseTenFalse =
  refl

balancedTritFieldSemanticsPreservesCarrier :
  balancedTritCarrierPreserved canonicalBalancedTritFieldSemanticsReceipt
  ≡ true
balancedTritFieldSemanticsPreservesCarrier =
  refl

balancedTritFieldSemanticsNoPromotion :
  BalancedTritFieldPromotion →
  ⊥
balancedTritFieldSemanticsNoPromotion =
  balancedTritFieldPromotionImpossibleHere
