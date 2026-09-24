{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTStressWeldBidiAttemptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld

------------------------------------------------------------------------
-- EXECUTABLE GR <-> QFT STRESS-WELD BIDI ATTEMPT
--
-- Promotion authority and executable comparison are deliberately distinct.
-- A missing promotion receipt is NOT a reason to avoid evaluating the two
-- actual stress-energy objects already carried by a UnifiedCandidate.
--
-- The application supplies only a residual algebra appropriate to its concrete
-- SharedStressEnergy carrier.  The probe then evaluates
--
--   residual
--     (GR literal stress mapped to the shared carrier)
--     (QFT total stress on the same candidate).
--
-- A later SameStressEnergyWeld may prove that residual zero is mandatory.
-- This module does not manufacture that theorem; it makes the attempted
-- comparison first-class even before promotion.
------------------------------------------------------------------------

data StressWeldAttemptOutcome : Set where
  exactResidualZero : StressWeldAttemptOutcome
  nonzeroResidualCounterexample : StressWeldAttemptOutcome

record SharedStressResidualProbe (U : Weld.UnifiedCandidate) : Set₁ where
  field
    Residual : Set
    zeroResidual : Residual
    residual :
      Weld.SharedStressEnergy U →
      Weld.SharedStressEnergy U →
      Residual
    residualIsZero : Residual → Bool
    reflexiveResidualZero :
      ∀ stress →
      residual stress stress ≡ zeroResidual
    reflexiveResidualClassifiesZero :
      ∀ stress →
      residualIsZero (residual stress stress) ≡ true

open SharedStressResidualProbe public

grSharedStressAt :
  (U : Weld.UnifiedCandidate) →
  Weld.Candidate U →
  Weld.SharedStressEnergy U
grSharedStressAt U candidate =
  Weld.grStressToShared U candidate
    (Weld.actualGRStressEnergy U candidate)

qftSharedStressAt :
  (U : Weld.UnifiedCandidate) →
  Weld.Candidate U →
  Weld.SharedStressEnergy U
qftSharedStressAt U candidate =
  Weld.qftTotalStressShared U candidate

stressWeldResidualAt :
  ∀ {U : Weld.UnifiedCandidate} →
  SharedStressResidualProbe U →
  Weld.Candidate U →
  SharedStressResidualProbe.Residual
stressWeldResidualAt {U} probe candidate =
  residual probe
    (grSharedStressAt U candidate)
    (qftSharedStressAt U candidate)

classifyResidualBool : Bool → StressWeldAttemptOutcome
classifyResidualBool true = exactResidualZero
classifyResidualBool false = nonzeroResidualCounterexample

stressWeldAttemptAt :
  ∀ {U : Weld.UnifiedCandidate}
    (probe : SharedStressResidualProbe U) →
  Weld.Candidate U →
  StressWeldAttemptOutcome
stressWeldAttemptAt probe candidate =
  classifyResidualBool
    (residualIsZero probe (stressWeldResidualAt probe candidate))

record StressWeldBidiAttemptReceipt
    (U : Weld.UnifiedCandidate)
    (probe : SharedStressResidualProbe U)
    (candidate : Weld.Candidate U) : Set₁ where
  constructor stressWeldBidiAttemptReceipt
  field
    grObject : Weld.SharedStressEnergy U
    qftObject : Weld.SharedStressEnergy U
    computedResidual : Residual probe
    outcome : StressWeldAttemptOutcome

    grObjectIsLiteral :
      grObject ≡ grSharedStressAt U candidate

    qftObjectIsLiteral :
      qftObject ≡ qftSharedStressAt U candidate

    residualIsLiteral :
      computedResidual ≡ stressWeldResidualAt probe candidate

    outcomeIsComputed :
      outcome ≡ stressWeldAttemptAt probe candidate

open StressWeldBidiAttemptReceipt public

runStressWeldBidiAttempt :
  ∀ {U : Weld.UnifiedCandidate}
    (probe : SharedStressResidualProbe U)
    (candidate : Weld.Candidate U) →
  StressWeldBidiAttemptReceipt U probe candidate
runStressWeldBidiAttempt {U} probe candidate =
  stressWeldBidiAttemptReceipt
    (grSharedStressAt U candidate)
    (qftSharedStressAt U candidate)
    (stressWeldResidualAt probe candidate)
    (stressWeldAttemptAt probe candidate)
    refl refl refl refl

bidiAttemptRunsWithoutPromotionReceipt : Bool
bidiAttemptRunsWithoutPromotionReceipt = true

bidiAttemptRunsWithoutPromotionReceiptIsTrue :
  bidiAttemptRunsWithoutPromotionReceipt ≡ true
bidiAttemptRunsWithoutPromotionReceiptIsTrue = refl

promotionStillRequiresTheoremBearingWeld : Bool
promotionStillRequiresTheoremBearingWeld = true

promotionStillRequiresTheoremBearingWeldIsTrue :
  promotionStillRequiresTheoremBearingWeld ≡ true
promotionStillRequiresTheoremBearingWeldIsTrue = refl

attemptBoundary : String
attemptBoundary =
  "Executable GR/QFT stress comparison is allowed before promotion; exact promotion still requires the theorem-bearing SameStressEnergyWeld and its physical calibration/continuum obligations."
