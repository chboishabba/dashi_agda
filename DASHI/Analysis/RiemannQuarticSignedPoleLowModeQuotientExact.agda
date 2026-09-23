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
  c4CarrierRegularity : LowModeQuotientCoordinate
  inverseFourthPsiDecay : LowModeQuotientCoordinate
  globalOddDefectsWellPosed : LowModeQuotientCoordinate
  globalLinearDefectZero : LowModeQuotientCoordinate
  globalCubicDefectZero : LowModeQuotientCoordinate
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
lowModeQuotientStatus c4CarrierRegularity = theoremOwned
lowModeQuotientStatus inverseFourthPsiDecay = theoremOwned
lowModeQuotientStatus globalOddDefectsWellPosed = theoremOwned
lowModeQuotientStatus globalLinearDefectZero = openAnalyticObstruction
lowModeQuotientStatus globalCubicDefectZero = openAnalyticObstruction
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
    c4CarrierRegularityPaid : Bool
    inverseFourthPsiDecayPaid : Bool
    globalOddDefectsWellPosedPaid : Bool
    globalLinearDefectZeroPaid : Bool
    globalCubicDefectZeroPaid : Bool

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
    c4CarrierRegularityPaidIsTrue :
      c4CarrierRegularityPaid ≡ true
    inverseFourthPsiDecayPaidIsTrue :
      inverseFourthPsiDecayPaid ≡ true
    globalOddDefectsWellPosedPaidIsTrue :
      globalOddDefectsWellPosedPaid ≡ true
    globalLinearDefectZeroPaidIsFalse :
      globalLinearDefectZeroPaid ≡ false
    globalCubicDefectZeroPaidIsFalse :
      globalCubicDefectZeroPaid ≡ false

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
    true
    true
    true
    false
    false
    false
    false
    false
    false
    true
    refl refl refl refl
    refl refl refl refl refl refl
    refl refl refl
    refl refl
    "The preferred symmetric Abel consumer is exactly invariant under adding a constant plus a centered quadratic discrepancy mode.  This is a genuine FactorsThrough result supplied by target-centred parity.  The local vanishing jet of Psi_t at t must not be promoted to invariance under arbitrary centered cubics.  The Lean companion now lifts the smooth bump carrier to C4, proves inverse-fourth decay for the actual Psi_t, makes the weighted cubic Psi moment globally integrable, and proves that the finite odd mode defects converge to concrete global Psi moments.  Their existence is paid; their vanishing is not."
    "The full global cubic quotient is now equivalent to two exact global equations: the global linear defect -integral Psi_t must vanish and the global cubic defect -3*integral Psi_t(x)*(x-t)^2 must vanish.  Investigate whether either equation follows from a same-object Fourier-inversion/profile identity, or whether cancellation only appears after coupling these obstruction coordinates to H_comb.  Do not infer either equation from the centered jet."

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
