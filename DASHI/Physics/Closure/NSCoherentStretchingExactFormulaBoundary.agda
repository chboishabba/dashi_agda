module DASHI.Physics.Closure.NSCoherentStretchingExactFormulaBoundary where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NS coherent stretching exact formula boundary.
--
-- Fail-closed receipt for the finite S2 formula
--
--   Omega_c dot S(c) Omega_c = lambda(c) (2 kappa^2 - 1).
--
-- With Y_c = sqrt(1 - kappa^2) e_+ + kappa e_- and
-- Omega_c = c cross (Y_c / |Y_c|), the cross-product rotation gives
-- Omega_c = sqrt(1 - kappa^2) e_- - kappa e_+.  Since the tangent strain
-- eigenvalues are +lambda on e_+ and -lambda on e_-, the displayed formula
-- follows.  Exact coherence kappa = 0 is compressive: -lambda.
--
-- This is a finite algebra receipt only; the PDE kappa-bias estimate is not
-- proved here.

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

data StretchingFormulaClause : Set where
  tangentBasisEPlusEMinus :
    StretchingFormulaClause
  ePlusEigenvaluePositiveLambda :
    StretchingFormulaClause
  eMinusEigenvalueNegativeLambda :
    StretchingFormulaClause
  lerayOutputDecomposesByKappa :
    StretchingFormulaClause
  crossProductRotatesOutputToVorticity :
    StretchingFormulaClause
  stretchingEqualsLambdaTimesTwoKappaSquaredMinusOne :
    StretchingFormulaClause
  coherentKappaZeroGivesNegativeLambda :
    StretchingFormulaClause
  stretchingThresholdAtOneOverSqrtTwo :
    StretchingFormulaClause

canonicalStretchingFormulaClauses :
  List StretchingFormulaClause
canonicalStretchingFormulaClauses =
  tangentBasisEPlusEMinus
  ∷ ePlusEigenvaluePositiveLambda
  ∷ eMinusEigenvalueNegativeLambda
  ∷ lerayOutputDecomposesByKappa
  ∷ crossProductRotatesOutputToVorticity
  ∷ stretchingEqualsLambdaTimesTwoKappaSquaredMinusOne
  ∷ coherentKappaZeroGivesNegativeLambda
  ∷ stretchingThresholdAtOneOverSqrtTwo
  ∷ []

stretchingFormulaClauseCount : Nat
stretchingFormulaClauseCount =
  listLength canonicalStretchingFormulaClauses

stretchingFormulaClauseCountIs8 :
  stretchingFormulaClauseCount ≡ 8
stretchingFormulaClauseCountIs8 =
  refl

data StretchingFormulaBoundaryGuard : Set where
  finiteS2SymbolFormulaOnly :
    StretchingFormulaBoundaryGuard
  monotoneLawRecordedAsFiniteConsequence :
    StretchingFormulaBoundaryGuard
  noLocalDefectMonotonicityFromFormulaAlone :
    StretchingFormulaBoundaryGuard
  noTriadicCompensatedLeakageIdentityFromFormulaAlone :
    StretchingFormulaBoundaryGuard
  noClayNavierStokesPromotion :
    StretchingFormulaBoundaryGuard

canonicalStretchingFormulaBoundaryGuards :
  List StretchingFormulaBoundaryGuard
canonicalStretchingFormulaBoundaryGuards =
  finiteS2SymbolFormulaOnly
  ∷ monotoneLawRecordedAsFiniteConsequence
  ∷ noLocalDefectMonotonicityFromFormulaAlone
  ∷ noTriadicCompensatedLeakageIdentityFromFormulaAlone
  ∷ noClayNavierStokesPromotion
  ∷ []

stretchingFormulaBoundaryGuardCount : Nat
stretchingFormulaBoundaryGuardCount =
  listLength canonicalStretchingFormulaBoundaryGuards

stretchingFormulaBoundaryGuardCountIs5 :
  stretchingFormulaBoundaryGuardCount ≡ 5
stretchingFormulaBoundaryGuardCountIs5 =
  refl

data NSCoherentStretchingPromotion : Set where

nsCoherentStretchingPromotionImpossibleHere :
  NSCoherentStretchingPromotion →
  ⊥
nsCoherentStretchingPromotionImpossibleHere ()

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

data NSCoherentStretchingExactFormulaStatus : Set where
  coherentStretchingFormulaRecorded_finiteAlgebra_noPromotion :
    NSCoherentStretchingExactFormulaStatus

nsCoherentStretchingExactFormulaSummary : String
nsCoherentStretchingExactFormulaSummary =
  "Records the finite S2 identity Omega_c dot S(c) Omega_c = lambda(c)(2 kappa^2 - 1), with kappa=0 giving -lambda; PDE kappa-bias and Clay promotion remain open/false."

record NSCoherentStretchingExactFormulaBoundary : Set where
  field
    status :
      NSCoherentStretchingExactFormulaStatus
    statusIsCanonical :
      status ≡ coherentStretchingFormulaRecorded_finiteAlgebra_noPromotion
    formulaClauses :
      List StretchingFormulaClause
    formulaClausesAreCanonical :
      formulaClauses ≡ canonicalStretchingFormulaClauses
    formulaClauseCountIsEight :
      stretchingFormulaClauseCount ≡ 8
    guards :
      List StretchingFormulaBoundaryGuard
    guardsAreCanonical :
      guards ≡ canonicalStretchingFormulaBoundaryGuards
    guardCountIsFive :
      stretchingFormulaBoundaryGuardCount ≡ 5
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionIsFalse :
      terminalPromotion ≡ false
    summary :
      String
    summaryIsCanonical :
      summary ≡ nsCoherentStretchingExactFormulaSummary

canonicalNSCoherentStretchingExactFormulaBoundary :
  NSCoherentStretchingExactFormulaBoundary
canonicalNSCoherentStretchingExactFormulaBoundary =
  record
    { status =
        coherentStretchingFormulaRecorded_finiteAlgebra_noPromotion
    ; statusIsCanonical =
        refl
    ; formulaClauses =
        canonicalStretchingFormulaClauses
    ; formulaClausesAreCanonical =
        refl
    ; formulaClauseCountIsEight =
        refl
    ; guards =
        canonicalStretchingFormulaBoundaryGuards
    ; guardsAreCanonical =
        refl
    ; guardCountIsFive =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalPromotionIsFalse =
        refl
    ; summary =
        nsCoherentStretchingExactFormulaSummary
    ; summaryIsCanonical =
        refl
    }

nsCoherentStretchingExactFormulaKeepsClayFalse :
  clayNavierStokesPromoted ≡ false
nsCoherentStretchingExactFormulaKeepsClayFalse =
  refl

nsCoherentStretchingExactFormulaKeepsTerminalFalse :
  terminalPromotion ≡ false
nsCoherentStretchingExactFormulaKeepsTerminalFalse =
  refl

