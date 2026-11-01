module DASHI.Physics.Closure.NSBiotSavartStrainMeanSquareExactFormulaBoundary where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NS Biot-Savart strain mean-square exact formula boundary.
--
-- Fail-closed receipt for the finite angular S2 calculation
--
--   (1 / 4 pi) int_{S2} lambda(c)^2 d sigma(c) = 11 / 60.
--
-- It records the exact mean-square coefficient only.  It deliberately does
-- not identify this with the mean strain <lambda>; RMS and L1 mean are kept
-- separate.  No PDE leakage square-function, continuum, Clay, or terminal
-- claim is promoted.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data ⊥ : Set where

data MeanSquareFormulaClause : Set where
  lambdaSquareAngularFormula :
    MeanSquareFormulaClause
  cosineTwoPhiCrossTermCancels :
    MeanSquareFormulaClause
  cosFourthWallisIntegralContributesTwoFifths :
    MeanSquareFormulaClause
  sinFifthWallisIntegralContributesSixteenFifteenths :
    MeanSquareFormulaClause
  normalizedSphereMeanEqualsElevenSixtieths :
    MeanSquareFormulaClause
  rootMeanSquareIsSqrtElevenSixtieths :
    MeanSquareFormulaClause
  lOneMeanLambdaNotDerivedFromMeanSquare :
    MeanSquareFormulaClause

canonicalMeanSquareFormulaClauses :
  List MeanSquareFormulaClause
canonicalMeanSquareFormulaClauses =
  lambdaSquareAngularFormula
  ∷ cosineTwoPhiCrossTermCancels
  ∷ cosFourthWallisIntegralContributesTwoFifths
  ∷ sinFifthWallisIntegralContributesSixteenFifteenths
  ∷ normalizedSphereMeanEqualsElevenSixtieths
  ∷ rootMeanSquareIsSqrtElevenSixtieths
  ∷ lOneMeanLambdaNotDerivedFromMeanSquare
  ∷ []

meanSquareFormulaClauseCount : Nat
meanSquareFormulaClauseCount =
  listLength canonicalMeanSquareFormulaClauses

meanSquareFormulaClauseCountIs7 :
  meanSquareFormulaClauseCount ≡ 7
meanSquareFormulaClauseCountIs7 =
  refl

data MeanSquarePromotionGuard : Set where
  finiteAngularIntegralOnly :
    MeanSquarePromotionGuard
  rmsCoefficientOnly :
    MeanSquarePromotionGuard
  noL1MeanPromotion :
    MeanSquarePromotionGuard
  noLeakageSquareFunctionIdentityPromotion :
    MeanSquarePromotionGuard
  noClayNavierStokesPromotion :
    MeanSquarePromotionGuard

canonicalMeanSquarePromotionGuards :
  List MeanSquarePromotionGuard
canonicalMeanSquarePromotionGuards =
  finiteAngularIntegralOnly
  ∷ rmsCoefficientOnly
  ∷ noL1MeanPromotion
  ∷ noLeakageSquareFunctionIdentityPromotion
  ∷ noClayNavierStokesPromotion
  ∷ []

meanSquarePromotionGuardCount : Nat
meanSquarePromotionGuardCount =
  listLength canonicalMeanSquarePromotionGuards

meanSquarePromotionGuardCountIs5 :
  meanSquarePromotionGuardCount ≡ 5
meanSquarePromotionGuardCountIs5 =
  refl

data NSBiotSavartStrainMeanSquarePromotion : Set where

nsBiotSavartStrainMeanSquarePromotionImpossibleHere :
  NSBiotSavartStrainMeanSquarePromotion →
  ⊥
nsBiotSavartStrainMeanSquarePromotionImpossibleHere ()

meanSquareFormulaPromotesLeakageIdentity : Bool
meanSquareFormulaPromotesLeakageIdentity =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

data NSBiotSavartStrainMeanSquareExactFormulaStatus : Set where
  biotSavartStrainMeanSquareRecorded_finiteExact_noPromotion :
    NSBiotSavartStrainMeanSquareExactFormulaStatus

nsBiotSavartStrainMeanSquareExactFormulaSummary : String
nsBiotSavartStrainMeanSquareExactFormulaSummary =
  "Records the finite angular mean-square strain coefficient <lambda^2>_{S2} = 11/60.  This gives an RMS coefficient, not the L1 mean, and promotes no leakage identity or Clay theorem."

record NSBiotSavartStrainMeanSquareExactFormulaBoundary : Set where
  field
    status :
      NSBiotSavartStrainMeanSquareExactFormulaStatus
    statusIsCanonical :
      status
        ≡ biotSavartStrainMeanSquareRecorded_finiteExact_noPromotion
    formulaClauses :
      List MeanSquareFormulaClause
    formulaClausesAreCanonical :
      formulaClauses ≡ canonicalMeanSquareFormulaClauses
    formulaClauseCountIsSeven :
      meanSquareFormulaClauseCount ≡ 7
    guards :
      List MeanSquarePromotionGuard
    guardsAreCanonical :
      guards ≡ canonicalMeanSquarePromotionGuards
    guardCountIsFive :
      meanSquarePromotionGuardCount ≡ 5
    meanSquareFormulaPromotesLeakageIdentityIsFalse :
      meanSquareFormulaPromotesLeakageIdentity ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionIsFalse :
      terminalPromotion ≡ false
    summary :
      String
    summaryIsCanonical :
      summary ≡ nsBiotSavartStrainMeanSquareExactFormulaSummary

canonicalNSBiotSavartStrainMeanSquareExactFormulaBoundary :
  NSBiotSavartStrainMeanSquareExactFormulaBoundary
canonicalNSBiotSavartStrainMeanSquareExactFormulaBoundary =
  record
    { status =
        biotSavartStrainMeanSquareRecorded_finiteExact_noPromotion
    ; statusIsCanonical =
        refl
    ; formulaClauses =
        canonicalMeanSquareFormulaClauses
    ; formulaClausesAreCanonical =
        refl
    ; formulaClauseCountIsSeven =
        refl
    ; guards =
        canonicalMeanSquarePromotionGuards
    ; guardsAreCanonical =
        refl
    ; guardCountIsFive =
        refl
    ; meanSquareFormulaPromotesLeakageIdentityIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalPromotionIsFalse =
        refl
    ; summary =
        nsBiotSavartStrainMeanSquareExactFormulaSummary
    ; summaryIsCanonical =
        refl
    }

nsBiotSavartStrainMeanSquareKeepsClayFalse :
  clayNavierStokesPromoted ≡ false
nsBiotSavartStrainMeanSquareKeepsClayFalse =
  refl

nsBiotSavartStrainMeanSquareKeepsTerminalFalse :
  terminalPromotion ≡ false
nsBiotSavartStrainMeanSquareKeepsTerminalFalse =
  refl

