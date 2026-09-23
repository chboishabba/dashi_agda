module DASHI.Analysis.RiemannQuarticSignedPoleLowModeQuotientExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RH G3 LOW-MODE QUOTIENT DIAGNOSTIC
--
-- Lean companion:
--
--   Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourthOrderQuotient.lean
--
-- The centered quartic jet is local information.  It does not by itself
-- imply that the global/symmetric Abel consumer is invariant under every
-- centered polynomial of degree <= 3.
--
-- The exact symmetric consumer does factor through the even low-mode
-- quotient
--
--   E ~ E + a0 + a2 (x-t)^2
--
-- because Psi_t' is odd about t.  A full cubic quotient additionally
-- requires the centered-linear and centered-cubic mode defects to vanish.
-- Those are retained as explicit analytic obstructions, not silently
-- promoted from the local jet.
------------------------------------------------------------------------

data LowModeQuotientCoordinate : Set where
  centeredDerivativeOdd : LowModeQuotientCoordinate
  constantModeInvisible : LowModeQuotientCoordinate
  quadraticModeInvisible : LowModeQuotientCoordinate
  evenLowModeFactorisation : LowModeQuotientCoordinate
  linearModeDefect : LowModeQuotientCoordinate
  cubicModeDefect : LowModeQuotientCoordinate
  fullCubicFactorisation : LowModeQuotientCoordinate
  localJetImpliesGlobalCubicFactorisation : LowModeQuotientCoordinate

data LowModeQuotientStatus : Set where
  theoremOwned : LowModeQuotientStatus
  openAnalyticObstruction : LowModeQuotientStatus
  rejectedPromotion : LowModeQuotientStatus

lowModeQuotientStatus :
  LowModeQuotientCoordinate -> LowModeQuotientStatus
lowModeQuotientStatus centeredDerivativeOdd = theoremOwned
lowModeQuotientStatus constantModeInvisible = theoremOwned
lowModeQuotientStatus quadraticModeInvisible = theoremOwned
lowModeQuotientStatus evenLowModeFactorisation = theoremOwned
lowModeQuotientStatus linearModeDefect = openAnalyticObstruction
lowModeQuotientStatus cubicModeDefect = openAnalyticObstruction
lowModeQuotientStatus fullCubicFactorisation = openAnalyticObstruction
lowModeQuotientStatus localJetImpliesGlobalCubicFactorisation = rejectedPromotion

record QuarticSignedPoleLowModeQuotientBoundary : Set where
  constructor quartic-signed-pole-low-mode-quotient-boundary
  field
    signedPsiDerivativeOddAboutTargetPaid : Bool
    constantDiscrepancyModeInvisiblePaid : Bool
    centeredQuadraticDiscrepancyModeInvisiblePaid : Bool
    evenLowModeQuotientFactorisationPaid : Bool

    centeredLinearModeDefectPaid : Bool
    centeredCubicModeDefectPaid : Bool
    fullCenteredCubicQuotientPaid : Bool

    localCenteredJetAloneProvesGlobalCubicQuotient : Bool
    fullCubicQuotientReducesToOddModeDefects : Bool

    signedPsiDerivativeOddAboutTargetPaidIsTrue :
      signedPsiDerivativeOddAboutTargetPaid ≡ true
    constantDiscrepancyModeInvisiblePaidIsTrue :
      constantDiscrepancyModeInvisiblePaid ≡ true
    centeredQuadraticDiscrepancyModeInvisiblePaidIsTrue :
      centeredQuadraticDiscrepancyModeInvisiblePaid ≡ true
    evenLowModeQuotientFactorisationPaidIsTrue :
      evenLowModeQuotientFactorisationPaid ≡ true

    centeredLinearModeDefectPaidIsFalse :
      centeredLinearModeDefectPaid ≡ false
    centeredCubicModeDefectPaidIsFalse :
      centeredCubicModeDefectPaid ≡ false
    fullCenteredCubicQuotientPaidIsFalse :
      fullCenteredCubicQuotientPaid ≡ false

    localCenteredJetAloneProvesGlobalCubicQuotientIsFalse :
      localCenteredJetAloneProvesGlobalCubicQuotient ≡ false
    fullCubicQuotientReducesToOddModeDefectsIsTrue :
      fullCubicQuotientReducesToOddModeDefects ≡ true

    interpretation : String
    nextResearchCut : String

canonicalQuarticSignedPoleLowModeQuotientBoundary :
  QuarticSignedPoleLowModeQuotientBoundary
canonicalQuarticSignedPoleLowModeQuotientBoundary =
  quartic-signed-pole-low-mode-quotient-boundary
    true
    true
    true
    true
    false
    false
    false
    false
    true
    refl refl refl refl
    refl refl refl
    refl refl
    "The preferred symmetric Abel consumer is exactly invariant under adding a constant plus a centered quadratic discrepancy mode.  This is a genuine FactorsThrough result supplied by target-centred parity.  The local vanishing jet of Psi_t at t must not be promoted to invariance under arbitrary centered cubics: linear and cubic discrepancy shifts survive as explicit global mode-defect coordinates."
    "Investigate the centered-linear and centered-cubic defects jointly with the horizontal remainder.  If those odd defects admit cancellation only after coupling to H_comb, that is the relevant fourth-order mechanism.  If they do not, the hoped-for full cubic quotient is unavailable on this route."

evenLowModeFactorisationIsPaid :
  lowModeQuotientStatus evenLowModeFactorisation ≡ theoremOwned
evenLowModeFactorisationIsPaid = refl

linearModeRemainsOpen :
  lowModeQuotientStatus linearModeDefect ≡ openAnalyticObstruction
linearModeRemainsOpen = refl

cubicModeRemainsOpen :
  lowModeQuotientStatus cubicModeDefect ≡ openAnalyticObstruction
cubicModeRemainsOpen = refl

localJetToGlobalCubicPromotionRejected :
  lowModeQuotientStatus localJetImpliesGlobalCubicFactorisation ≡ rejectedPromotion
localJetToGlobalCubicPromotionRejected = refl
