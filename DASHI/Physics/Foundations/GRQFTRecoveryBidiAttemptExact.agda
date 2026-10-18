{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTRecoveryBidiAttemptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.BianchiLovelockCompletion as GR
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld

------------------------------------------------------------------------
-- RECOVERED-VS-TARGET BIDI PROBES
--
-- The theorem-bearing GRRecoveryReceipt/QFTRecoveryReceipt require equality.
-- This module deliberately runs before those receipts: applications provide a
-- residual on the actual carrier and we evaluate recovered object vs selected
-- target on the same coarse-grained candidate.
------------------------------------------------------------------------

data RecoveryAttemptOutcome : Set where
  exactRecoveryResidualZero : RecoveryAttemptOutcome
  nonzeroRecoveryCounterexample : RecoveryAttemptOutcome

classifyRecoveryBool : Bool → RecoveryAttemptOutcome
classifyRecoveryBool true = exactRecoveryResidualZero
classifyRecoveryBool false = nonzeroRecoveryCounterexample

record GRRecoveryResidualProbe (U : Weld.UnifiedCandidate) : Set₁ where
  field
    Residual : Set
    residual :
      GR.EinsteinContinuumClosure →
      GR.EinsteinContinuumClosure →
      Residual
    residualIsZero : Residual → Bool


grRecoveredAfterCoarseGraining :
  (U : Weld.UnifiedCandidate) →
  Weld.Candidate U →
  Weld.Regime U →
  GR.EinsteinContinuumClosure
grRecoveredAfterCoarseGraining U candidate regime =
  Weld.recoverGR U
    (Weld.microscopicState U (Weld.coarseGrain U candidate regime))

grSelectedTargetAfterCoarseGraining :
  (U : Weld.UnifiedCandidate) →
  Weld.Candidate U →
  Weld.Regime U →
  GR.EinsteinContinuumClosure
grSelectedTargetAfterCoarseGraining U candidate regime =
  Weld.grTarget U (Weld.coarseGrain U candidate regime)

grRecoveryResidualAt :
  ∀ {U : Weld.UnifiedCandidate} →
  GRRecoveryResidualProbe U →
  Weld.Candidate U →
  Weld.Regime U →
  GRRecoveryResidualProbe.Residual probe
grRecoveryResidualAt {U} probe candidate regime =
  GRRecoveryResidualProbe.residual probe
    (grRecoveredAfterCoarseGraining U candidate regime)
    (grSelectedTargetAfterCoarseGraining U candidate regime)

runGRRecoveryAttempt :
  ∀ {U : Weld.UnifiedCandidate}
    (probe : GRRecoveryResidualProbe U) →
  Weld.Candidate U →
  Weld.Regime U →
  RecoveryAttemptOutcome
runGRRecoveryAttempt probe candidate regime =
  classifyRecoveryBool
    (GRRecoveryResidualProbe.residualIsZero probe
      (grRecoveryResidualAt probe candidate regime))

record QFTRecoveryResidualProbe (U : Weld.UnifiedCandidate) : Set₁ where
  field
    Residual : Set
    residual :
      QFT.LiteralYangMillsConstruction
        (Weld.qftCarriers U) (Weld.qftSemantics U) →
      QFT.LiteralYangMillsConstruction
        (Weld.qftCarriers U) (Weld.qftSemantics U) →
      Residual
    residualIsZero : Residual → Bool


qftRecoveredAfterCoarseGraining :
  (U : Weld.UnifiedCandidate) →
  Weld.Candidate U →
  Weld.Regime U →
  QFT.LiteralYangMillsConstruction
    (Weld.qftCarriers U) (Weld.qftSemantics U)
qftRecoveredAfterCoarseGraining U candidate regime =
  Weld.recoverQFT U
    (Weld.microscopicState U (Weld.coarseGrain U candidate regime))

qftSelectedTargetAfterCoarseGraining :
  (U : Weld.UnifiedCandidate) →
  Weld.Candidate U →
  Weld.Regime U →
  QFT.LiteralYangMillsConstruction
    (Weld.qftCarriers U) (Weld.qftSemantics U)
qftSelectedTargetAfterCoarseGraining U candidate regime =
  Weld.qftTarget U (Weld.coarseGrain U candidate regime)

qftRecoveryResidualAt :
  ∀ {U : Weld.UnifiedCandidate} →
  QFTRecoveryResidualProbe U →
  Weld.Candidate U →
  Weld.Regime U →
  QFTRecoveryResidualProbe.Residual probe
qftRecoveryResidualAt {U} probe candidate regime =
  QFTRecoveryResidualProbe.residual probe
    (qftRecoveredAfterCoarseGraining U candidate regime)
    (qftSelectedTargetAfterCoarseGraining U candidate regime)

runQFTRecoveryAttempt :
  ∀ {U : Weld.UnifiedCandidate}
    (probe : QFTRecoveryResidualProbe U) →
  Weld.Candidate U →
  Weld.Regime U →
  RecoveryAttemptOutcome
runQFTRecoveryAttempt probe candidate regime =
  classifyRecoveryBool
    (QFTRecoveryResidualProbe.residualIsZero probe
      (qftRecoveryResidualAt probe candidate regime))

recoveryAttemptsDoNotRequirePromotionTokens : Bool
recoveryAttemptsDoNotRequirePromotionTokens = true

recoveryAttemptsDoNotRequirePromotionTokensIsTrue :
  recoveryAttemptsDoNotRequirePromotionTokens ≡ true
recoveryAttemptsDoNotRequirePromotionTokensIsTrue = refl
