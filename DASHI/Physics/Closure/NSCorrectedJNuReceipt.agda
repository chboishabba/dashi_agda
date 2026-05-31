module DASHI.Physics.Closure.NSCorrectedJNuReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Corrected Navier-Stokes dissipation-cutoff j_nu receipt.
--
-- This receipt records the corrected cutoff after making the Bernstein
-- constant explicit as sqrt(p).  The prior NSBandODECorrectedReceipt kept
-- the 11/8 bookkeeping offset with an unspecified universal C0.  Absorbing
-- the explicit sqrt(p) factor adds 1/2, so
--
--   j_nu = log_p(C0/nu) + 11/8
--        = log_p(sqrt(p)/nu) + 11/8
--        = log_p(1/nu) + 15/8.
--
-- This is a cutoff bookkeeping correction only.  It introduces no Clay,
-- global regularity, or terminal promotion.

data NSCorrectedJNuStatus : Set where
  correctedDissipationCutoffRecorded :
    NSCorrectedJNuStatus

  sqrtPBernsteinConstantAbsorbed :
    NSCorrectedJNuStatus

  priorElevenEighthsBookkeepingRecorded :
    NSCorrectedJNuStatus

  explicitHalfCorrectionRecorded :
    NSCorrectedJNuStatus

  correctedFifteenEighthsOffsetRecorded :
    NSCorrectedJNuStatus

  p2ExplicitTableRecorded :
    NSCorrectedJNuStatus

  noClayGlobalOrTerminalPromotion :
    NSCorrectedJNuStatus

canonicalNSCorrectedJNuStatus :
  List NSCorrectedJNuStatus
canonicalNSCorrectedJNuStatus =
  correctedDissipationCutoffRecorded
  ∷ sqrtPBernsteinConstantAbsorbed
  ∷ priorElevenEighthsBookkeepingRecorded
  ∷ explicitHalfCorrectionRecorded
  ∷ correctedFifteenEighthsOffsetRecorded
  ∷ p2ExplicitTableRecorded
  ∷ noClayGlobalOrTerminalPromotion
  ∷ []

data CorrectedJNuFormula : Set where
  logPInvNuPlusFifteenEighths :
    CorrectedJNuFormula

data PriorCorrection : Set where
  priorElevenEighthsPlusExplicitSqrtPHalf :
    PriorCorrection

data ExplicitTableStatus : Set where
  recorded :
    ExplicitTableStatus

data P2JNuTableRow : Set where
  p2Nu0001JNu1184 :
    P2JNuTableRow

  p2Nu001JNu852 :
    P2JNuTableRow

  p2Nu01JNu520 :
    P2JNuTableRow

  p2Nu10JNu1875 :
    P2JNuTableRow

canonicalP2JNuTable :
  List P2JNuTableRow
canonicalP2JNuTable =
  p2Nu0001JNu1184
  ∷ p2Nu001JNu852
  ∷ p2Nu01JNu520
  ∷ p2Nu10JNu1875
  ∷ []

data NSCorrectedJNuPromotion : Set where

nsCorrectedJNuPromotionImpossibleHere :
  NSCorrectedJNuPromotion →
  ⊥
nsCorrectedJNuPromotionImpossibleHere ()

correctedJNuFormulaText : String
correctedJNuFormulaText =
  "j_nu = log_p(1/nu) + 15/8"

correctedJNuEqualityChainText : String
correctedJNuEqualityChainText =
  "j_nu = log_p(C0/nu)+11/8 = log_p(sqrt(p)/nu)+11/8 = log_p(1/nu)+15/8"

sqrtPBernsteinAbsorptionText : String
sqrtPBernsteinAbsorptionText =
  "C0 is made explicit as sqrt(p), contributing log_p(sqrt(p)) = 1/2"

priorCorrectionText : String
priorCorrectionText =
  "Prior NSBandODECorrectedReceipt used 11/8 bookkeeping with unspecified C0; explicit sqrt(p) factor adds 1/2"

p2ExplicitTableText : String
p2ExplicitTableText =
  "p=2: nu=0.001 => j_nu=11.84; nu=0.01 => j_nu=8.52; nu=0.1 => j_nu=5.20; nu=1.0 => j_nu=1.875"

nsCorrectedJNuStatement : String
nsCorrectedJNuStatement =
  "Corrected NS cutoff records j_nu = log_p(C0/nu)+11/8 = log_p(sqrt(p)/nu)+11/8 = log_p(1/nu)+15/8.  The prior 11/8 bookkeeping used unspecified C0; making C0=sqrt(p) explicit adds 1/2.  The p=2 explicit table is recorded.  No Clay, global regularity, or terminal promotion follows."

record NSCorrectedJNuReceipt : Setω where
  field
    status :
      List NSCorrectedJNuStatus

    statusIsCanonical :
      status ≡ canonicalNSCorrectedJNuStatus

    correctedJNu :
      String

    correctedJNuIsCanonical :
      correctedJNu ≡ correctedJNuFormulaText

    correctedJNuFormula :
      CorrectedJNuFormula

    correctedJNuFormulaIsCanonical :
      correctedJNuFormula ≡ logPInvNuPlusFifteenEighths

    correctedJNuEqualityChain :
      String

    correctedJNuEqualityChainIsCanonical :
      correctedJNuEqualityChain ≡ correctedJNuEqualityChainText

    sqrtPBernsteinConstantAbsorbedFlag :
      Bool

    sqrtPBernsteinConstantAbsorbedFlagIsTrue :
      sqrtPBernsteinConstantAbsorbedFlag ≡ true

    sqrtPBernsteinAbsorption :
      String

    sqrtPBernsteinAbsorptionIsCanonical :
      sqrtPBernsteinAbsorption ≡ sqrtPBernsteinAbsorptionText

    priorRecordCorrection :
      PriorCorrection

    priorRecordCorrectionIsCanonical :
      priorRecordCorrection ≡ priorElevenEighthsPlusExplicitSqrtPHalf

    priorRecordCorrectionTextLabel :
      String

    priorRecordCorrectionTextLabelIsCanonical :
      priorRecordCorrectionTextLabel ≡ priorCorrectionText

    priorOffsetNumerator :
      Nat

    priorOffsetNumeratorIs11 :
      priorOffsetNumerator ≡ 11

    priorOffsetDenominator :
      Nat

    priorOffsetDenominatorIs8 :
      priorOffsetDenominator ≡ 8

    explicitSqrtPHalfNumerator :
      Nat

    explicitSqrtPHalfNumeratorIs1 :
      explicitSqrtPHalfNumerator ≡ 1

    explicitSqrtPHalfDenominator :
      Nat

    explicitSqrtPHalfDenominatorIs2 :
      explicitSqrtPHalfDenominator ≡ 2

    correctedOffsetNumerator :
      Nat

    correctedOffsetNumeratorIs15 :
      correctedOffsetNumerator ≡ 15

    correctedOffsetDenominator :
      Nat

    correctedOffsetDenominatorIs8 :
      correctedOffsetDenominator ≡ 8

    explicitTable :
      ExplicitTableStatus

    explicitTableIsRecorded :
      explicitTable ≡ recorded

    p2Table :
      List P2JNuTableRow

    p2TableIsCanonical :
      p2Table ≡ canonicalP2JNuTable

    p2TableText :
      String

    p2TableTextIsCanonical :
      p2TableText ≡ p2ExplicitTableText

    tablePrime :
      Nat

    tablePrimeIs2 :
      tablePrime ≡ 2

    row1NuTimes1000 :
      Nat

    row1NuTimes1000Is1 :
      row1NuTimes1000 ≡ 1

    row1JNuTimes1000 :
      Nat

    row1JNuTimes1000Is11840 :
      row1JNuTimes1000 ≡ 11840

    row2NuTimes100 :
      Nat

    row2NuTimes100Is1 :
      row2NuTimes100 ≡ 1

    row2JNuTimes100 :
      Nat

    row2JNuTimes100Is852 :
      row2JNuTimes100 ≡ 852

    row3NuTimes10 :
      Nat

    row3NuTimes10Is1 :
      row3NuTimes10 ≡ 1

    row3JNuTimes100 :
      Nat

    row3JNuTimes100Is520 :
      row3JNuTimes100 ≡ 520

    row4NuTimes1 :
      Nat

    row4NuTimes1Is1 :
      row4NuTimes1 ≡ 1

    row4JNuTimes1000 :
      Nat

    row4JNuTimes1000Is1875 :
      row4JNuTimes1000 ≡ 1875

    noClayPromotion :
      Bool

    noClayPromotionIsTrue :
      noClayPromotion ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    terminalPromotionPromoted :
      Bool

    terminalPromotionPromotedIsFalse :
      terminalPromotionPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsCorrectedJNuStatement

    promotionFlags :
      List NSCorrectedJNuPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSCorrectedJNuReceipt public

canonicalNSCorrectedJNuReceipt :
  NSCorrectedJNuReceipt
canonicalNSCorrectedJNuReceipt =
  record
    { status =
        canonicalNSCorrectedJNuStatus
    ; statusIsCanonical =
        refl
    ; correctedJNu =
        correctedJNuFormulaText
    ; correctedJNuIsCanonical =
        refl
    ; correctedJNuFormula =
        logPInvNuPlusFifteenEighths
    ; correctedJNuFormulaIsCanonical =
        refl
    ; correctedJNuEqualityChain =
        correctedJNuEqualityChainText
    ; correctedJNuEqualityChainIsCanonical =
        refl
    ; sqrtPBernsteinConstantAbsorbedFlag =
        true
    ; sqrtPBernsteinConstantAbsorbedFlagIsTrue =
        refl
    ; sqrtPBernsteinAbsorption =
        sqrtPBernsteinAbsorptionText
    ; sqrtPBernsteinAbsorptionIsCanonical =
        refl
    ; priorRecordCorrection =
        priorElevenEighthsPlusExplicitSqrtPHalf
    ; priorRecordCorrectionIsCanonical =
        refl
    ; priorRecordCorrectionTextLabel =
        priorCorrectionText
    ; priorRecordCorrectionTextLabelIsCanonical =
        refl
    ; priorOffsetNumerator =
        11
    ; priorOffsetNumeratorIs11 =
        refl
    ; priorOffsetDenominator =
        8
    ; priorOffsetDenominatorIs8 =
        refl
    ; explicitSqrtPHalfNumerator =
        1
    ; explicitSqrtPHalfNumeratorIs1 =
        refl
    ; explicitSqrtPHalfDenominator =
        2
    ; explicitSqrtPHalfDenominatorIs2 =
        refl
    ; correctedOffsetNumerator =
        15
    ; correctedOffsetNumeratorIs15 =
        refl
    ; correctedOffsetDenominator =
        8
    ; correctedOffsetDenominatorIs8 =
        refl
    ; explicitTable =
        recorded
    ; explicitTableIsRecorded =
        refl
    ; p2Table =
        canonicalP2JNuTable
    ; p2TableIsCanonical =
        refl
    ; p2TableText =
        p2ExplicitTableText
    ; p2TableTextIsCanonical =
        refl
    ; tablePrime =
        2
    ; tablePrimeIs2 =
        refl
    ; row1NuTimes1000 =
        1
    ; row1NuTimes1000Is1 =
        refl
    ; row1JNuTimes1000 =
        11840
    ; row1JNuTimes1000Is11840 =
        refl
    ; row2NuTimes100 =
        1
    ; row2NuTimes100Is1 =
        refl
    ; row2JNuTimes100 =
        852
    ; row2JNuTimes100Is852 =
        refl
    ; row3NuTimes10 =
        1
    ; row3NuTimes10Is1 =
        refl
    ; row3JNuTimes100 =
        520
    ; row3JNuTimes100Is520 =
        refl
    ; row4NuTimes1 =
        1
    ; row4NuTimes1Is1 =
        refl
    ; row4JNuTimes1000 =
        1875
    ; row4JNuTimes1000Is1875 =
        refl
    ; noClayPromotion =
        true
    ; noClayPromotionIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; terminalPromotionPromoted =
        false
    ; terminalPromotionPromotedIsFalse =
        refl
    ; statement =
        nsCorrectedJNuStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "correctedJNu = log_p(1/nu) + 15/8"
        ∷ "j_nu = log_p(C0/nu)+11/8 = log_p(sqrt(p)/nu)+11/8 = log_p(1/nu)+15/8"
        ∷ "prior NSBandODECorrectedReceipt used 11/8 bookkeeping with unspecified C0"
        ∷ "explicit sqrt(p) factor adds 1/2, giving 15/8"
        ∷ "explicitTable = recorded"
        ∷ "p=2 table: nu=0.001 -> 11.84; nu=0.01 -> 8.52; nu=0.1 -> 5.20; nu=1.0 -> 1.875"
        ∷ "No Clay, global regularity, or terminal promotion is made"
        ∷ []
    }

correctedJNuFormulaRecorded :
  correctedJNu canonicalNSCorrectedJNuReceipt
  ≡
  correctedJNuFormulaText
correctedJNuFormulaRecorded =
  refl

correctedJNuOffsetIsFifteenOverEight :
  correctedOffsetNumerator canonicalNSCorrectedJNuReceipt ≡ 15
correctedJNuOffsetIsFifteenOverEight =
  refl

explicitTableRecorded :
  explicitTable canonicalNSCorrectedJNuReceipt ≡ recorded
explicitTableRecorded =
  refl

p2TableRecorded :
  p2Table canonicalNSCorrectedJNuReceipt ≡ canonicalP2JNuTable
p2TableRecorded =
  refl

nsCorrectedJNuDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSCorrectedJNuReceipt ≡ false
nsCorrectedJNuDoesNotPromoteClay =
  refl

nsCorrectedJNuDoesNotPromoteGlobalRegularity :
  globalRegularityPromoted canonicalNSCorrectedJNuReceipt ≡ false
nsCorrectedJNuDoesNotPromoteGlobalRegularity =
  refl

nsCorrectedJNuDoesNotPromoteTerminal :
  terminalPromotionPromoted canonicalNSCorrectedJNuReceipt ≡ false
nsCorrectedJNuDoesNotPromoteTerminal =
  refl

nsCorrectedJNuNoPromotion :
  NSCorrectedJNuPromotion →
  ⊥
nsCorrectedJNuNoPromotion =
  nsCorrectedJNuPromotionImpossibleHere
