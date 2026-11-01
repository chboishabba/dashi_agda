module DASHI.Physics.Closure.NSResidualAlignmentObstructionHierarchyReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- NS residual alignment obstruction hierarchy receipt.
--
-- This module records the sharpened residual obstruction hierarchy R1/R2/R3
-- in fail-closed receipt form:
--
--   R1: pressure-correction dominance when delta1 is small
--   R2: uniform delta1 lower bound as the exact remaining quantitative gate
--       for L3-a
--   R3: H_area remains open via determinant-side Cauchy-Schwarz
--
-- The receipt is intentionally non-promoting.  It keeps the open gate and
-- obstruction lanes explicit, records canonical rows, and leaves theorem and
-- Clay promotion false.

data Void : Set where

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Local carriers for the residual hierarchy.

data PressureCorrectionCarrier : Set where
  pressureCorrectionDominanceForSmallDelta1Carrier :
    PressureCorrectionCarrier

data Delta1GateCarrier : Set where
  uniformDelta1LowerBoundForL3aCarrier :
    Delta1GateCarrier

data HAreaObstructionCarrier : Set where
  determinantSideCauchySchwarzOpenCarrier :
    HAreaObstructionCarrier

data NSResidualAlignmentObstructionPromotion : Set where

residualAlignmentObstructionPromotionImpossibleHere :
  NSResidualAlignmentObstructionPromotion →
  Void
residualAlignmentObstructionPromotionImpossibleHere ()

data NSResidualAlignmentObstructionGateRow : Set where
  r1PressureCorrectionDominanceRecorded :
    NSResidualAlignmentObstructionGateRow
  r2UniformDelta1LowerBoundGateRecorded :
    NSResidualAlignmentObstructionGateRow
  r3HAreaDeterminantSideCauchySchwarzOpenRecorded :
    NSResidualAlignmentObstructionGateRow
  theoremPromotionBlockedRecorded :
    NSResidualAlignmentObstructionGateRow
  clayPromotionBlockedRecorded :
    NSResidualAlignmentObstructionGateRow

canonicalNSResidualAlignmentObstructionGateRows :
  List NSResidualAlignmentObstructionGateRow
canonicalNSResidualAlignmentObstructionGateRows =
  r1PressureCorrectionDominanceRecorded
  ∷ r2UniformDelta1LowerBoundGateRecorded
  ∷ r3HAreaDeterminantSideCauchySchwarzOpenRecorded
  ∷ theoremPromotionBlockedRecorded
  ∷ clayPromotionBlockedRecorded
  ∷ []

data NSResidualAlignmentObstructionBlocker : Set where
  uniformDelta1LowerBoundForL3aOpen :
    NSResidualAlignmentObstructionBlocker
  hAreaDeterminantSideCauchySchwarzOpen :
    NSResidualAlignmentObstructionBlocker

canonicalNSResidualAlignmentObstructionBlockers :
  List NSResidualAlignmentObstructionBlocker
canonicalNSResidualAlignmentObstructionBlockers =
  uniformDelta1LowerBoundForL3aOpen
  ∷ hAreaDeterminantSideCauchySchwarzOpen
  ∷ []

------------------------------------------------------------------------
-- Canonical O/R/C/S/L/P/G/F strings.

organizationString : String
organizationString =
  "O: Worker lane 5 records the NS residual alignment obstruction hierarchy as a fail-closed receipt."

requirementString : String
requirementString =
  "R: R1 records pressure-correction dominance when delta1 is small; R2 records the uniform delta1 lower bound as the exact remaining quantitative gate for L3-a; R3 keeps H_area open via determinant-side Cauchy-Schwarz."

codeArtifactString : String
codeArtifactString =
  "C: This standalone Agda receipt owns only the local carriers, the compact gate table, the blocker ledger, and the false promotion flags."

stateString : String
stateString =
  "S: R1 support is retained, R2 remains the live quantitative gate for L3-a, and R3 remains open by determinant-side Cauchy-Schwarz; theorem promotion and Clay promotion stay false."

latticeString : String
latticeString =
  "L: small delta1 -> pressure-correction dominance -> uniform delta1 lower bound for L3-a -> determinant-side Cauchy-Schwarz keeps H_area open -> blocked promotion."

proposalString : String
proposalString =
  "P: Treat this as a receipt-only hierarchy ledger; any closure beyond the recorded residual lanes must come from a separate theorem-bearing route."

governanceString : String
governanceString =
  "G: Fail closed: the receipt records the sharpened residual hierarchy, keeps the exact remaining gate explicit, and does not assert theorem promotion."

gapString : String
gapString =
  "F: Remaining gap is the uniform delta1 lower bound for L3-a together with the determinant-side Cauchy-Schwarz H_area obstruction; theorem and Clay promotion remain false."

record NSResidualAlignmentObstructionORCSLPGF : Set where
  constructor nsResidualAlignmentObstructionORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ gapString

canonicalNSResidualAlignmentObstructionORCSLPGF :
  NSResidualAlignmentObstructionORCSLPGF
canonicalNSResidualAlignmentObstructionORCSLPGF =
  nsResidualAlignmentObstructionORCSLPGF
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
    refl

------------------------------------------------------------------------
-- Compact gate table text and canonical carriers.

r1PressureCorrectionDominanceText : String
r1PressureCorrectionDominanceText =
  "R1: pressure-correction dominance is recorded for the small-delta1 regime."

r2UniformDelta1LowerBoundText : String
r2UniformDelta1LowerBoundText =
  "R2: uniform delta1 lower bound is the exact remaining quantitative gate for L3-a."

r3HAreaDeterminantSideCauchySchwarzText : String
r3HAreaDeterminantSideCauchySchwarzText =
  "R3: H_area remains open via determinant-side Cauchy-Schwarz."

theoremPromotionBlockedText : String
theoremPromotionBlockedText =
  "theorem promotion stays false"

clayPromotionBlockedText : String
clayPromotionBlockedText =
  "Clay promotion stays false"

nsResidualAlignmentObstructionStatement : String
nsResidualAlignmentObstructionStatement =
  "The receipt records the sharpened residual obstruction hierarchy R1/R2/R3: pressure-correction dominance when delta1 is small, the uniform delta1 lower bound as the exact remaining quantitative gate for L3-a, and H_area still open via determinant-side Cauchy-Schwarz. No theorem promotion is claimed."

canonicalPressureCorrectionCarrier :
  PressureCorrectionCarrier
canonicalPressureCorrectionCarrier =
  pressureCorrectionDominanceForSmallDelta1Carrier

canonicalDelta1GateCarrier :
  Delta1GateCarrier
canonicalDelta1GateCarrier =
  uniformDelta1LowerBoundForL3aCarrier

canonicalHAreaObstructionCarrier :
  HAreaObstructionCarrier
canonicalHAreaObstructionCarrier =
  determinantSideCauchySchwarzOpenCarrier

canonicalR1PressureCorrectionDominanceRecorded : Bool
canonicalR1PressureCorrectionDominanceRecorded =
  true

canonicalR2UniformDelta1LowerBoundGateRecorded : Bool
canonicalR2UniformDelta1LowerBoundGateRecorded =
  true

canonicalR3HAreaDeterminantSideCauchySchwarzOpenRecorded : Bool
canonicalR3HAreaDeterminantSideCauchySchwarzOpenRecorded =
  true

canonicalTheoremPromotion : Bool
canonicalTheoremPromotion =
  false

canonicalClayPromotion : Bool
canonicalClayPromotion =
  false

record NSResidualAlignmentObstructionReceipt : Setω where
  field
    gateRows :
      List NSResidualAlignmentObstructionGateRow
    gateRowsAreCanonical :
      gateRows ≡ canonicalNSResidualAlignmentObstructionGateRows
    gateRowCount :
      Nat
    gateRowCountIsCanonical :
      gateRowCount ≡ listLength canonicalNSResidualAlignmentObstructionGateRows
    pressureCorrectionCarrier :
      PressureCorrectionCarrier
    pressureCorrectionCarrierIsCanonical :
      pressureCorrectionCarrier ≡ canonicalPressureCorrectionCarrier
    delta1GateCarrier :
      Delta1GateCarrier
    delta1GateCarrierIsCanonical :
      delta1GateCarrier ≡ canonicalDelta1GateCarrier
    hAreaObstructionCarrier :
      HAreaObstructionCarrier
    hAreaObstructionCarrierIsCanonical :
      hAreaObstructionCarrier ≡ canonicalHAreaObstructionCarrier
    blockers :
      List NSResidualAlignmentObstructionBlocker
    blockersAreCanonical :
      blockers ≡ canonicalNSResidualAlignmentObstructionBlockers
    blockerCount :
      Nat
    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSResidualAlignmentObstructionBlockers
    r1PressureCorrectionDominanceRecordedFlag :
      Bool
    r1PressureCorrectionDominanceRecordedFlagIsTrue :
      r1PressureCorrectionDominanceRecordedFlag ≡ true
    r2UniformDelta1LowerBoundGateRecordedFlag :
      Bool
    r2UniformDelta1LowerBoundGateRecordedFlagIsTrue :
      r2UniformDelta1LowerBoundGateRecordedFlag ≡ true
    r3HAreaDeterminantSideCauchySchwarzOpenRecordedFlag :
      Bool
    r3HAreaDeterminantSideCauchySchwarzOpenRecordedFlagIsTrue :
      r3HAreaDeterminantSideCauchySchwarzOpenRecordedFlag ≡ true
    theoremPromotion :
      Bool
    theoremPromotionIsFalse :
      theoremPromotion ≡ false
    clayPromotion :
      Bool
    clayPromotionIsFalse :
      clayPromotion ≡ false
    orcslpgf :
      NSResidualAlignmentObstructionORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSResidualAlignmentObstructionORCSLPGF
    statement :
      String
    statementIsCanonical :
      statement ≡ nsResidualAlignmentObstructionStatement
    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡
        r1PressureCorrectionDominanceText
        ∷ r2UniformDelta1LowerBoundText
        ∷ r3HAreaDeterminantSideCauchySchwarzText
        ∷ theoremPromotionBlockedText
        ∷ clayPromotionBlockedText
        ∷ []
    promotionFlags :
      List NSResidualAlignmentObstructionPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open NSResidualAlignmentObstructionReceipt public

canonicalNSResidualAlignmentObstructionReceipt :
  NSResidualAlignmentObstructionReceipt
canonicalNSResidualAlignmentObstructionReceipt =
  record
    { gateRows =
        canonicalNSResidualAlignmentObstructionGateRows
    ; gateRowsAreCanonical =
        refl
    ; gateRowCount =
        listLength canonicalNSResidualAlignmentObstructionGateRows
    ; gateRowCountIsCanonical =
        refl
    ; pressureCorrectionCarrier =
        canonicalPressureCorrectionCarrier
    ; pressureCorrectionCarrierIsCanonical =
        refl
    ; delta1GateCarrier =
        canonicalDelta1GateCarrier
    ; delta1GateCarrierIsCanonical =
        refl
    ; hAreaObstructionCarrier =
        canonicalHAreaObstructionCarrier
    ; hAreaObstructionCarrierIsCanonical =
        refl
    ; blockers =
        canonicalNSResidualAlignmentObstructionBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listLength canonicalNSResidualAlignmentObstructionBlockers
    ; blockerCountIsCanonical =
        refl
    ; r1PressureCorrectionDominanceRecordedFlag =
        canonicalR1PressureCorrectionDominanceRecorded
    ; r1PressureCorrectionDominanceRecordedFlagIsTrue =
        refl
    ; r2UniformDelta1LowerBoundGateRecordedFlag =
        canonicalR2UniformDelta1LowerBoundGateRecorded
    ; r2UniformDelta1LowerBoundGateRecordedFlagIsTrue =
        refl
    ; r3HAreaDeterminantSideCauchySchwarzOpenRecordedFlag =
        canonicalR3HAreaDeterminantSideCauchySchwarzOpenRecorded
    ; r3HAreaDeterminantSideCauchySchwarzOpenRecordedFlagIsTrue =
        refl
    ; theoremPromotion =
        canonicalTheoremPromotion
    ; theoremPromotionIsFalse =
        refl
    ; clayPromotion =
        canonicalClayPromotion
    ; clayPromotionIsFalse =
        refl
    ; orcslpgf =
        canonicalNSResidualAlignmentObstructionORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    ; statement =
        nsResidualAlignmentObstructionStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        r1PressureCorrectionDominanceText
        ∷ r2UniformDelta1LowerBoundText
        ∷ r3HAreaDeterminantSideCauchySchwarzText
        ∷ theoremPromotionBlockedText
        ∷ clayPromotionBlockedText
        ∷ []
    ; receiptBoundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

gateRowsCountIs5 :
  gateRowCount canonicalNSResidualAlignmentObstructionReceipt ≡ 5
gateRowsCountIs5 =
  refl

blockersCountIs2 :
  blockerCount canonicalNSResidualAlignmentObstructionReceipt ≡ 2
blockersCountIs2 =
  refl

theoremPromotionFalse :
  theoremPromotion canonicalNSResidualAlignmentObstructionReceipt ≡ false
theoremPromotionFalse =
  refl

clayPromotionFalse :
  clayPromotion canonicalNSResidualAlignmentObstructionReceipt ≡ false
clayPromotionFalse =
  refl
