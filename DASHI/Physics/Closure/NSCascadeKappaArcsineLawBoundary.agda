module DASHI.Physics.Closure.NSCascadeKappaArcsineLawBoundary where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NS cascade kappa arcsine law boundary.
--
-- Fail-closed receipt for the corrected finite NS statistical package.
-- It records the finite S2 propagated-polarization law:
--
--   kappa = cos theta, theta uniform on a circle,
--   density dkappa / (pi sqrt(1 - kappa^2)),
--   Pr(|kappa| < epsilon) = (2 / pi) arcsin epsilon,
--   E kappa = 0, E kappa^2 = 1 / 2, E kappa^4 = 3 / 8.
--
-- This replaces the earlier informal "uniform kappa" interpretation.  The
-- module records only a finite-statistical boundary and promotes no PDE,
-- Navier-Stokes, Clay, continuum, or terminal theorem.

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

data KappaArcsineLawClause : Set where
  propagatedPolarizationAngleUniformOnCircle :
    KappaArcsineLawClause
  kappaIsCosineOfPolarizationAngle :
    KappaArcsineLawClause
  arcsineDensityOnMinusOneOne :
    KappaArcsineLawClause
  coherentFractionTwoOverPiArcsinEpsilon :
    KappaArcsineLawClause
  firstMomentZero :
    KappaArcsineLawClause
  secondMomentOneHalf :
    KappaArcsineLawClause
  fourthMomentThreeEighths :
    KappaArcsineLawClause

canonicalKappaArcsineLawClauses :
  List KappaArcsineLawClause
canonicalKappaArcsineLawClauses =
  propagatedPolarizationAngleUniformOnCircle
  ∷ kappaIsCosineOfPolarizationAngle
  ∷ arcsineDensityOnMinusOneOne
  ∷ coherentFractionTwoOverPiArcsinEpsilon
  ∷ firstMomentZero
  ∷ secondMomentOneHalf
  ∷ fourthMomentThreeEighths
  ∷ []

kappaArcsineLawClauseCount : Nat
kappaArcsineLawClauseCount =
  listLength canonicalKappaArcsineLawClauses

kappaArcsineLawClauseCountIs7 :
  kappaArcsineLawClauseCount ≡ 7
kappaArcsineLawClauseCountIs7 =
  refl

data KappaArcsineCorrectionGuard : Set where
  replacesUniformDistributionClaim :
    KappaArcsineCorrectionGuard
  backgroundCoherentFractionIsOrderEpsilon :
    KappaArcsineCorrectionGuard
  finiteCascadeDoesNotSelectCoherence :
    KappaArcsineCorrectionGuard
  noCoherentDominationTheoremFromThisLaw :
    KappaArcsineCorrectionGuard
  pdeKappaBiasBoundStillOpen :
    KappaArcsineCorrectionGuard

canonicalKappaArcsineCorrectionGuards :
  List KappaArcsineCorrectionGuard
canonicalKappaArcsineCorrectionGuards =
  replacesUniformDistributionClaim
  ∷ backgroundCoherentFractionIsOrderEpsilon
  ∷ finiteCascadeDoesNotSelectCoherence
  ∷ noCoherentDominationTheoremFromThisLaw
  ∷ pdeKappaBiasBoundStillOpen
  ∷ []

kappaArcsineCorrectionGuardCount : Nat
kappaArcsineCorrectionGuardCount =
  listLength canonicalKappaArcsineCorrectionGuards

kappaArcsineCorrectionGuardCountIs5 :
  kappaArcsineCorrectionGuardCount ≡ 5
kappaArcsineCorrectionGuardCountIs5 =
  refl

data KappaArcsinePromotion : Set where

kappaArcsinePromotionImpossibleHere :
  KappaArcsinePromotion →
  ⊥
kappaArcsinePromotionImpossibleHere ()

finiteStatisticalStatusOnly : Bool
finiteStatisticalStatusOnly =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

data NSCascadeKappaArcsineLawStatus : Set where
  kappaArcsineLawRecorded_finiteStatistical_noPromotion :
    NSCascadeKappaArcsineLawStatus

nsCascadeKappaArcsineLawSummary : String
nsCascadeKappaArcsineLawSummary =
  "Finite S2 propagated-polarization kappa follows the arcsine law, not the uniform law; this fixes the neutral baseline for later PDE kappa-bias targets and promotes no NS/Clay theorem."

record NSCascadeKappaArcsineLawBoundary : Set where
  field
    status :
      NSCascadeKappaArcsineLawStatus
    statusIsCanonical :
      status ≡ kappaArcsineLawRecorded_finiteStatistical_noPromotion
    lawClauses :
      List KappaArcsineLawClause
    lawClausesAreCanonical :
      lawClauses ≡ canonicalKappaArcsineLawClauses
    lawClauseCountIsSeven :
      kappaArcsineLawClauseCount ≡ 7
    correctionGuards :
      List KappaArcsineCorrectionGuard
    correctionGuardsAreCanonical :
      correctionGuards ≡ canonicalKappaArcsineCorrectionGuards
    correctionGuardCountIsFive :
      kappaArcsineCorrectionGuardCount ≡ 5
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionIsFalse :
      terminalPromotion ≡ false
    summary :
      String
    summaryIsCanonical :
      summary ≡ nsCascadeKappaArcsineLawSummary

canonicalNSCascadeKappaArcsineLawBoundary :
  NSCascadeKappaArcsineLawBoundary
canonicalNSCascadeKappaArcsineLawBoundary =
  record
    { status =
        kappaArcsineLawRecorded_finiteStatistical_noPromotion
    ; statusIsCanonical =
        refl
    ; lawClauses =
        canonicalKappaArcsineLawClauses
    ; lawClausesAreCanonical =
        refl
    ; lawClauseCountIsSeven =
        refl
    ; correctionGuards =
        canonicalKappaArcsineCorrectionGuards
    ; correctionGuardsAreCanonical =
        refl
    ; correctionGuardCountIsFive =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalPromotionIsFalse =
        refl
    ; summary =
        nsCascadeKappaArcsineLawSummary
    ; summaryIsCanonical =
        refl
    }

nsCascadeKappaArcsineLawKeepsClayFalse :
  clayNavierStokesPromoted ≡ false
nsCascadeKappaArcsineLawKeepsClayFalse =
  refl

nsCascadeKappaArcsineLawKeepsTerminalFalse :
  terminalPromotion ≡ false
nsCascadeKappaArcsineLawKeepsTerminalFalse =
  refl

