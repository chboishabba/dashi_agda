module DASHI.Physics.Closure.NSBoundCorrectionJNuReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Navier-Stokes j_nu cutoff correction receipt.
--
-- This receipt corrects the cutoff bookkeeping from the earlier local band
-- ODE receipt.  The previous display kept the constant as C0 and wrote the
-- cutoff as
--
--   j_nu = log_p(C0 / nu) + 11/8.
--
-- In the corrected normalization, C0 is sqrt(p).  Absorbing sqrt(p) into the
-- p-adic logarithmic exponent contributes +1/2 = +4/8.  The cutoff offset
-- therefore shifts from 11/8 to 15/8:
--
--   j_nu = log_p(1 / nu) + 15/8.
--
-- This is only a bookkeeping correction for the threshold.  It makes no
-- Navier-Stokes Clay, global regularity, or terminal promotion claim.

data Void : Set where

infixr 5 _::_

data List (A : Set) : Set where
  [] :
    List A

  _::_ :
    A ->
    List A ->
    List A

data NSBoundCorrectionStatus : Set where
  priorCutoffRecorded :
    NSBoundCorrectionStatus

  c0NormalisationCorrectedToSqrtP :
    NSBoundCorrectionStatus

  sqrtPAbsorptionShiftRecorded :
    NSBoundCorrectionStatus

  correctedJNuOffsetRecorded :
    NSBoundCorrectionStatus

  correctedJNuFormulaRecorded :
    NSBoundCorrectionStatus

  noClayPromotionStatus :
    NSBoundCorrectionStatus

canonicalNSBoundCorrectionStatus :
  List NSBoundCorrectionStatus
canonicalNSBoundCorrectionStatus =
  priorCutoffRecorded
  :: c0NormalisationCorrectedToSqrtP
  :: sqrtPAbsorptionShiftRecorded
  :: correctedJNuOffsetRecorded
  :: correctedJNuFormulaRecorded
  :: noClayPromotionStatus
  :: []

data PriorCutoff : Set where
  logPOfC0OverNuPlusElevenEighths :
    PriorCutoff

data CorrectedC0 : Set where
  sqrtP :
    CorrectedC0

data AbsorbedExponentShift : Set where
  oneHalfFromSqrtP :
    AbsorbedExponentShift

data CorrectedJNu : Set where
  logPOfOneOverNuPlusFifteenEighths :
    CorrectedJNu

data ClayPromotionGate : Set where
  clayNavierStokesGate :
    ClayPromotionGate

  globalRegularityGate :
    ClayPromotionGate

  terminalClayClaimGate :
    ClayPromotionGate

data NSBoundCorrectionPromotion : Set where

nsBoundCorrectionPromotionImpossibleHere :
  NSBoundCorrectionPromotion ->
  Void
nsBoundCorrectionPromotionImpossibleHere ()

priorCutoffFormula : String
priorCutoffFormula =
  "prior j_nu = log_p(C0 / nu) + 11/8"

c0CorrectionFormula : String
c0CorrectionFormula =
  "corrected C0 = sqrt(p)"

sqrtPShiftFormula : String
sqrtPShiftFormula =
  "absorbing sqrt(p) contributes +1/2 = +4/8 to the cutoff offset"

correctedOffsetFormula : String
correctedOffsetFormula =
  "11/8 + 1/2 = 15/8"

correctedJNuFormula : String
correctedJNuFormula =
  "corrected j_nu = log_p(1 / nu) + 15/8"

nsBoundCorrectionStatement : String
nsBoundCorrectionStatement =
  "Corrected NS cutoff bookkeeping: the prior cutoff log_p(C0/nu)+11/8 is replaced because C0=sqrt(p). Absorbing sqrt(p) gives a +1/2 shift, so j_nu = log_p(1/nu)+15/8. No Clay Navier-Stokes, global regularity, or terminal Clay promotion follows."

record NSBoundCorrectionJNuReceipt : Setω where
  field
    status :
      List NSBoundCorrectionStatus

    statusIsCanonical :
      status ≡ canonicalNSBoundCorrectionStatus

    priorCutoff :
      PriorCutoff

    priorCutoffIsCanonical :
      priorCutoff ≡ logPOfC0OverNuPlusElevenEighths

    priorCutoffFormulaLabel :
      String

    priorCutoffFormulaLabelIsCanonical :
      priorCutoffFormulaLabel ≡ priorCutoffFormula

    correctedC0 :
      CorrectedC0

    correctedC0IsSqrtP :
      correctedC0 ≡ sqrtP

    correctedC0FormulaLabel :
      String

    correctedC0FormulaLabelIsCanonical :
      correctedC0FormulaLabel ≡ c0CorrectionFormula

    absorbedShift :
      AbsorbedExponentShift

    absorbedShiftIsOneHalfFromSqrtP :
      absorbedShift ≡ oneHalfFromSqrtP

    absorbedShiftFormulaLabel :
      String

    absorbedShiftFormulaLabelIsCanonical :
      absorbedShiftFormulaLabel ≡ sqrtPShiftFormula

    priorOffsetNumerator :
      Nat

    priorOffsetNumeratorIs11 :
      priorOffsetNumerator ≡ 11

    priorOffsetDenominator :
      Nat

    priorOffsetDenominatorIs8 :
      priorOffsetDenominator ≡ 8

    sqrtPShiftNumeratorOverCommonDenominator :
      Nat

    sqrtPShiftNumeratorOverCommonDenominatorIs4 :
      sqrtPShiftNumeratorOverCommonDenominator ≡ 4

    sqrtPShiftDenominator :
      Nat

    sqrtPShiftDenominatorIs8 :
      sqrtPShiftDenominator ≡ 8

    correctedOffsetNumerator :
      Nat

    correctedOffsetNumeratorIs15 :
      correctedOffsetNumerator ≡ 15

    correctedOffsetDenominator :
      Nat

    correctedOffsetDenominatorIs8 :
      correctedOffsetDenominator ≡ 8

    offsetArithmetic :
      priorOffsetNumerator + sqrtPShiftNumeratorOverCommonDenominator
      ≡ correctedOffsetNumerator

    correctedOffsetFormulaLabel :
      String

    correctedOffsetFormulaLabelIsCanonical :
      correctedOffsetFormulaLabel ≡ correctedOffsetFormula

    correctedJNu :
      CorrectedJNu

    correctedJNuIsCanonical :
      correctedJNu ≡ logPOfOneOverNuPlusFifteenEighths

    correctedJNuFormulaLabel :
      String

    correctedJNuFormulaLabelIsCanonical :
      correctedJNuFormulaLabel ≡ correctedJNuFormula

    clayNavierStokesGateOpen :
      Bool

    clayNavierStokesGateOpenIsFalse :
      clayNavierStokesGateOpen ≡ false

    globalRegularityGateOpen :
      Bool

    globalRegularityGateOpenIsFalse :
      globalRegularityGateOpen ≡ false

    terminalClayClaimGateOpen :
      Bool

    terminalClayClaimGateOpenIsFalse :
      terminalClayClaimGateOpen ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List NSBoundCorrectionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    falseClayPromotionGates :
      List ClayPromotionGate

    statement :
      String

    statementIsCanonical :
      statement ≡ nsBoundCorrectionStatement

    receiptBoundary :
      List String

open NSBoundCorrectionJNuReceipt public

canonicalNSBoundCorrectionJNuReceipt :
  NSBoundCorrectionJNuReceipt
canonicalNSBoundCorrectionJNuReceipt =
  record
    { status =
        canonicalNSBoundCorrectionStatus
    ; statusIsCanonical =
        refl
    ; priorCutoff =
        logPOfC0OverNuPlusElevenEighths
    ; priorCutoffIsCanonical =
        refl
    ; priorCutoffFormulaLabel =
        priorCutoffFormula
    ; priorCutoffFormulaLabelIsCanonical =
        refl
    ; correctedC0 =
        sqrtP
    ; correctedC0IsSqrtP =
        refl
    ; correctedC0FormulaLabel =
        c0CorrectionFormula
    ; correctedC0FormulaLabelIsCanonical =
        refl
    ; absorbedShift =
        oneHalfFromSqrtP
    ; absorbedShiftIsOneHalfFromSqrtP =
        refl
    ; absorbedShiftFormulaLabel =
        sqrtPShiftFormula
    ; absorbedShiftFormulaLabelIsCanonical =
        refl
    ; priorOffsetNumerator =
        11
    ; priorOffsetNumeratorIs11 =
        refl
    ; priorOffsetDenominator =
        8
    ; priorOffsetDenominatorIs8 =
        refl
    ; sqrtPShiftNumeratorOverCommonDenominator =
        4
    ; sqrtPShiftNumeratorOverCommonDenominatorIs4 =
        refl
    ; sqrtPShiftDenominator =
        8
    ; sqrtPShiftDenominatorIs8 =
        refl
    ; correctedOffsetNumerator =
        15
    ; correctedOffsetNumeratorIs15 =
        refl
    ; correctedOffsetDenominator =
        8
    ; correctedOffsetDenominatorIs8 =
        refl
    ; offsetArithmetic =
        refl
    ; correctedOffsetFormulaLabel =
        correctedOffsetFormula
    ; correctedOffsetFormulaLabelIsCanonical =
        refl
    ; correctedJNu =
        logPOfOneOverNuPlusFifteenEighths
    ; correctedJNuIsCanonical =
        refl
    ; correctedJNuFormulaLabel =
        correctedJNuFormula
    ; correctedJNuFormulaLabelIsCanonical =
        refl
    ; clayNavierStokesGateOpen =
        false
    ; clayNavierStokesGateOpenIsFalse =
        refl
    ; globalRegularityGateOpen =
        false
    ; globalRegularityGateOpenIsFalse =
        refl
    ; terminalClayClaimGateOpen =
        false
    ; terminalClayClaimGateOpenIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; falseClayPromotionGates =
        clayNavierStokesGate
        :: globalRegularityGate
        :: terminalClayClaimGate
        :: []
    ; statement =
        nsBoundCorrectionStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Prior cutoff recorded as log_p(C0/nu)+11/8"
        :: "Corrected normalization records C0=sqrt(p)"
        :: "Absorbing sqrt(p) contributes +1/2 to the p-adic cutoff exponent"
        :: "The offset shifts from 11/8 to 15/8"
        :: "Corrected cutoff recorded as j_nu=log_p(1/nu)+15/8"
        :: "Clay Navier-Stokes, global regularity, and terminal Clay promotion gates remain false"
        :: []
    }

priorCutoffWasElevenEighths :
  priorOffsetNumerator canonicalNSBoundCorrectionJNuReceipt ≡ 11
priorCutoffWasElevenEighths =
  refl

sqrtPAbsorptionAddsOneHalf :
  sqrtPShiftNumeratorOverCommonDenominator
    canonicalNSBoundCorrectionJNuReceipt
  ≡ 4
sqrtPAbsorptionAddsOneHalf =
  refl

correctedJNuOffsetIsFifteenEighths :
  correctedOffsetNumerator canonicalNSBoundCorrectionJNuReceipt ≡ 15
correctedJNuOffsetIsFifteenEighths =
  refl

correctedJNuFormulaIsRecorded :
  correctedJNuFormulaLabel canonicalNSBoundCorrectionJNuReceipt
  ≡
  correctedJNuFormula
correctedJNuFormulaIsRecorded =
  refl

nsBoundCorrectionDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSBoundCorrectionJNuReceipt ≡ false
nsBoundCorrectionDoesNotPromoteClay =
  refl

nsBoundCorrectionDoesNotPromoteGlobalRegularity :
  globalRegularityPromoted canonicalNSBoundCorrectionJNuReceipt ≡ false
nsBoundCorrectionDoesNotPromoteGlobalRegularity =
  refl

nsBoundCorrectionDoesNotPromoteTerminalClayClaim :
  terminalClayClaimPromoted canonicalNSBoundCorrectionJNuReceipt ≡ false
nsBoundCorrectionDoesNotPromoteTerminalClayClaim =
  refl

nsBoundCorrectionNoPromotion :
  NSBoundCorrectionPromotion ->
  Void
nsBoundCorrectionNoPromotion =
  nsBoundCorrectionPromotionImpossibleHere
