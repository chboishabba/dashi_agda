module DASHI.Physics.Closure.ClayKPCorrectedSeriesIdentityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.ClaySolvedLedgerLemmas as Solved
import DASHI.Physics.Closure.ClayNumericPrecisionCorrectionReceipt as Precision

------------------------------------------------------------------------
-- Connected-animal KP corrected series identity receipt.
--
-- This receipt records the formula-selection and promotion-governance facts
-- that are currently inhabitable in Agda.  It deliberately does not claim to
-- formalise the analytic infinite-series proof inside Agda.

data KPCorrectedSeriesIdentityStatus : Set where
  kpCorrectedSeriesIdentityRecorded_noPromotion :
    KPCorrectedSeriesIdentityStatus

data KPSeriesExpression : Set where
  connectedAnimalDepthSum :
    KPSeriesExpression

  correctedClosedForm :
    KPSeriesExpression

  legacyWrongClosedForm :
    KPSeriesExpression

canonicalKPSeriesExpressions : List KPSeriesExpression
canonicalKPSeriesExpressions =
  connectedAnimalDepthSum
  ∷ correctedClosedForm
  ∷ legacyWrongClosedForm
  ∷ []

expressionText : KPSeriesExpression → String
expressionText connectedAnimalDepthSum =
  "sum_{d>=1} d*p^(d-1)*q^d"
expressionText correctedClosedForm =
  "q/(1-p*q)^2"
expressionText legacyWrongClosedForm =
  "p*q/(1-p*q)^2"

connectedAnimalDepthSumTextIsCanonical :
  expressionText connectedAnimalDepthSum
  ≡
  "sum_{d>=1} d*p^(d-1)*q^d"
connectedAnimalDepthSumTextIsCanonical =
  refl

correctedClosedFormTextIsQOverOneMinusPqSquared :
  expressionText correctedClosedForm ≡ "q/(1-p*q)^2"
correctedClosedFormTextIsQOverOneMinusPqSquared =
  refl

legacyWrongClosedFormTextIsPqOverOneMinusPqSquared :
  expressionText legacyWrongClosedForm ≡ "p*q/(1-p*q)^2"
legacyWrongClosedFormTextIsPqOverOneMinusPqSquared =
  refl

data KPFormulaRole : Set where
  primaryConnectedAnimalKPFormula :
    KPFormulaRole

  rejectedLegacyFormula :
    KPFormulaRole

formulaRole : KPSeriesExpression → KPFormulaRole
formulaRole connectedAnimalDepthSum =
  primaryConnectedAnimalKPFormula
formulaRole correctedClosedForm =
  primaryConnectedAnimalKPFormula
formulaRole legacyWrongClosedForm =
  rejectedLegacyFormula

connectedAnimalDepthSumIsPrimary :
  formulaRole connectedAnimalDepthSum ≡ primaryConnectedAnimalKPFormula
connectedAnimalDepthSumIsPrimary =
  refl

correctedClosedFormIsPrimary :
  formulaRole correctedClosedForm ≡ primaryConnectedAnimalKPFormula
correctedClosedFormIsPrimary =
  refl

legacyWrongClosedFormIsRejected :
  formulaRole legacyWrongClosedForm ≡ rejectedLegacyFormula
legacyWrongClosedFormIsRejected =
  refl

correctedClosedFormAllowedAsKPRoute : Bool
correctedClosedFormAllowedAsKPRoute =
  true

legacyWrongClosedFormAllowedAsKPRoute : Bool
legacyWrongClosedFormAllowedAsKPRoute =
  false

correctedClosedFormAllowedAsKPRouteIsTrue :
  correctedClosedFormAllowedAsKPRoute ≡ true
correctedClosedFormAllowedAsKPRouteIsTrue =
  refl

legacyWrongClosedFormAllowedAsKPRouteIsFalse :
  legacyWrongClosedFormAllowedAsKPRoute ≡ false
legacyWrongClosedFormAllowedAsKPRouteIsFalse =
  refl

------------------------------------------------------------------------
-- The corrected formula supports KP convergence bookkeeping only.

data KPSeriesConsequence : Set where
  connectedAnimalKPConvergenceOnly :
    KPSeriesConsequence

  notStrictBalabanSeed :
    KPSeriesConsequence

  notClayPromotion :
    KPSeriesConsequence

canonicalKPSeriesConsequences : List KPSeriesConsequence
canonicalKPSeriesConsequences =
  connectedAnimalKPConvergenceOnly
  ∷ notStrictBalabanSeed
  ∷ notClayPromotion
  ∷ []

correctedFormulaProvesBalabanSeed : Bool
correctedFormulaProvesBalabanSeed =
  false

correctedFormulaProvesClayYangMills : Bool
correctedFormulaProvesClayYangMills =
  false

correctedFormulaProvesBalabanSeedIsFalse :
  correctedFormulaProvesBalabanSeed ≡ false
correctedFormulaProvesBalabanSeedIsFalse =
  refl

correctedFormulaProvesClayYangMillsIsFalse :
  correctedFormulaProvesClayYangMills ≡ false
correctedFormulaProvesClayYangMillsIsFalse =
  refl

data KPSeriesIdentityPromotion : Set where

kpSeriesIdentityPromotionImpossibleHere :
  KPSeriesIdentityPromotion →
  ⊥
kpSeriesIdentityPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Precision constants consumed from the solved ledger.

connectedAnimalSafeThresholdMillis : Nat
connectedAnimalSafeThresholdMillis =
  Solved.connectedAnimalThresholdMillis

connectedAnimalThresholdMillionths : Nat
connectedAnimalThresholdMillionths =
  Precision.connectedAnimalThresholdMillionths

connectedAnimalGapMillionths : Nat
connectedAnimalGapMillionths =
  Precision.connectedAnimalGapMillionths

connectedAnimalSafeThresholdMillisIs9594 :
  connectedAnimalSafeThresholdMillis ≡ 9594
connectedAnimalSafeThresholdMillisIs9594 =
  refl

connectedAnimalThresholdMillionthsIs9593637 :
  connectedAnimalThresholdMillionths ≡ 9593637
connectedAnimalThresholdMillionthsIs9593637 =
  refl

connectedAnimalGapMillionthsIs3593637 :
  connectedAnimalGapMillionths ≡ 3593637
connectedAnimalGapMillionthsIs3593637 =
  refl

kpSeriesIdentitySummary : String
kpSeriesIdentitySummary =
  "Connected-animal KP formula correction: sum_{d>=1} d*p^(d-1)*q^d is recorded as q/(1-p*q)^2. The old p*q/(1-p*q)^2 form is rejected. This supports connected-animal KP convergence bookkeeping at beta=9.593637 and does not prove strict Balaban seed, Balaban transfer, or Clay YM."

kpSeriesIdentityBoundary : String
kpSeriesIdentityBoundary =
  "This receipt records the corrected formula choice and governance consequences only. It does not formalise the analytic infinite-series theorem in Agda and does not inhabit any Clay-grade analytic lemma."

record ClayKPCorrectedSeriesIdentityReceipt : Setω where
  field
    status :
      KPCorrectedSeriesIdentityStatus

    statusIsCanonical :
      status ≡ kpCorrectedSeriesIdentityRecorded_noPromotion

    expressions :
      List KPSeriesExpression

    expressionsAreCanonical :
      expressions ≡ canonicalKPSeriesExpressions

    correctedFormula :
      String

    correctedFormulaIsQOverOneMinusPqSquared :
      correctedFormula ≡ expressionText correctedClosedForm

    legacyFormula :
      String

    legacyFormulaIsRejectedForm :
      legacyFormula ≡ expressionText legacyWrongClosedForm

    correctedFormulaAllowed :
      correctedClosedFormAllowedAsKPRoute ≡ true

    legacyFormulaRejected :
      legacyWrongClosedFormAllowedAsKPRoute ≡ false

    solvedLedger :
      Solved.connectedAnimalThresholdMillis ≡ 9594

    numericPrecisionReceipt :
      Precision.ClayNumericPrecisionCorrectionReceipt

    numericPrecisionNoYMClay :
      Precision.ClayNumericPrecisionCorrectionReceipt.clayYangMillsPromoted
        numericPrecisionReceipt
      ≡
      false

    caThresholdMillionths :
      Nat

    caThresholdMillionthsIs9593637 :
      caThresholdMillionths ≡ Precision.connectedAnimalThresholdMillionths

    caGapMillionths :
      Nat

    caGapMillionthsIs3593637 :
      caGapMillionths ≡ Precision.connectedAnimalGapMillionths

    consequences :
      List KPSeriesConsequence

    consequencesAreCanonical :
      consequences ≡ canonicalKPSeriesConsequences

    balabanSeedProved :
      Bool

    balabanSeedProvedIsFalse :
      balabanSeedProved ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    receiptBoundary :
      List String

canonicalClayKPCorrectedSeriesIdentityReceipt :
  ClayKPCorrectedSeriesIdentityReceipt
canonicalClayKPCorrectedSeriesIdentityReceipt =
  record
    { status =
        kpCorrectedSeriesIdentityRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; expressions =
        canonicalKPSeriesExpressions
    ; expressionsAreCanonical =
        refl
    ; correctedFormula =
        expressionText correctedClosedForm
    ; correctedFormulaIsQOverOneMinusPqSquared =
        refl
    ; legacyFormula =
        expressionText legacyWrongClosedForm
    ; legacyFormulaIsRejectedForm =
        refl
    ; correctedFormulaAllowed =
        refl
    ; legacyFormulaRejected =
        refl
    ; solvedLedger =
        refl
    ; numericPrecisionReceipt =
        Precision.canonicalClayNumericPrecisionCorrectionReceipt
    ; numericPrecisionNoYMClay =
        refl
    ; caThresholdMillionths =
        Precision.connectedAnimalThresholdMillionths
    ; caThresholdMillionthsIs9593637 =
        refl
    ; caGapMillionths =
        Precision.connectedAnimalGapMillionths
    ; caGapMillionthsIs3593637 =
        refl
    ; consequences =
        canonicalKPSeriesConsequences
    ; consequencesAreCanonical =
        refl
    ; balabanSeedProved =
        false
    ; balabanSeedProvedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; receiptBoundary =
        kpSeriesIdentityBoundary
        ∷ "Correct formula: sum_{d>=1} d*p^(d-1)*q^d = q/(1-p*q)^2."
        ∷ "Rejected legacy formula: p*q/(1-p*q)^2."
        ∷ "The beta=9.593637 threshold is connected-animal KP convergence only."
        ∷ "Strict Balaban seed still requires beta*c_min-a>log(2p), or a robust numeric sample such as beta_eff>=13.7."
        ∷ "All Clay, YM, Gate3, W4, gravity, and terminal promotions remain false."
        ∷ []
    }

canonicalKPCorrectedSeriesKeepsPromotionsFalse :
  ClayKPCorrectedSeriesIdentityReceipt.clayYangMillsPromoted
    canonicalClayKPCorrectedSeriesIdentityReceipt
  ≡
  false
canonicalKPCorrectedSeriesKeepsPromotionsFalse =
  refl
