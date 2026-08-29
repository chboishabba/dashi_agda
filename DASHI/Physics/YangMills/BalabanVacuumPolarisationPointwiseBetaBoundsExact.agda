{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanVacuumPolarisationPointwiseBetaBoundsExact where

------------------------------------------------------------------------
-- ROUND101: THE ACTUAL CMP109 (5.42) OBJECT IS ALREADY IN THE DYNAMICS TYPE
--
-- `BalabanCutoffCouplingDynamics` does not leave betaCorrection arbitrary: its
-- `vacuumPolarisationCoefficient` contains CMP109 (5.42), namely
--
--   betaCorrection_(k+1)
--     = negativeOffDiagonalSecondMomentumDerivative_k,     k < K.
--
-- Hence the shortest literal Row-A producer should NOT assume another beta
-- correspondence theorem.  It should prove two-sided estimates directly for
-- this already-named mixed second derivative on the actual generated history.
-- This file transports those source estimates to the recurrence correction.
--
-- The Ward-patch / constrained-Gaussian calculation and the finite-g normalized
-- interaction calculation therefore meet at exactly one source-native scalar:
-- `negativeOffDiagonalSecondMomentumDerivative`.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Nat.Base as ℕ

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_; _<ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory as Trajectory
import DASHI.Physics.YangMills.BalabanCutoffBetaLaw as BetaLaw

record LiteralVacuumPolarisationPointwiseBounds
    {K : Nat}
    (dynamics : BetaLaw.BalabanCutoffCouplingDynamics K) : Set₁ where
  field
    betaLower betaUpper : ℝ
    betaLowerPositive : DASHI.Foundations.RealAnalysisAxioms.0ℝ <ℝ betaLower
    betaLowerBelowUpper : betaLower ≤ℝ betaUpper

    derivativeLower :
      ∀ k → k ℕ.< K →
      betaLower ≤ℝ
        BetaLaw.negativeOffDiagonalSecondMomentumDerivative
          (BetaLaw.vacuumPolarisationCoefficient dynamics) k

    derivativeUpper :
      ∀ k → k ℕ.< K →
      BetaLaw.negativeOffDiagonalSecondMomentumDerivative
        (BetaLaw.vacuumPolarisationCoefficient dynamics) k
      ≤ℝ betaUpper

open LiteralVacuumPolarisationPointwiseBounds public

betaCorrectionIsLiteralMixedDerivative :
  ∀ {K}
    (dynamics : BetaLaw.BalabanCutoffCouplingDynamics K)
    k → (k<K : k ℕ.< K) →
  Trajectory.betaCorrection (BetaLaw.step dynamics) (suc k)
  ≡ BetaLaw.negativeOffDiagonalSecondMomentumDerivative
      (BetaLaw.vacuumPolarisationCoefficient dynamics) k
betaCorrectionIsLiteralMixedDerivative dynamics =
  BetaLaw.betaFromVacuumPolarisation
    (BetaLaw.vacuumPolarisationCoefficient dynamics)

betaCorrectionLowerFromLiteralDerivative :
  ∀ {K} {dynamics : BetaLaw.BalabanCutoffCouplingDynamics K}
    (bounds : LiteralVacuumPolarisationPointwiseBounds dynamics)
    k → (k<K : k ℕ.< K) →
  betaLower bounds ≤ℝ
    Trajectory.betaCorrection (BetaLaw.step dynamics) (suc k)
betaCorrectionLowerFromLiteralDerivative {dynamics = dynamics} bounds k k<K
  rewrite betaCorrectionIsLiteralMixedDerivative dynamics k k<K =
  derivativeLower bounds k k<K

betaCorrectionUpperFromLiteralDerivative :
  ∀ {K} {dynamics : BetaLaw.BalabanCutoffCouplingDynamics K}
    (bounds : LiteralVacuumPolarisationPointwiseBounds dynamics)
    k → (k<K : k ℕ.< K) →
  Trajectory.betaCorrection (BetaLaw.step dynamics) (suc k)
    ≤ℝ betaUpper bounds
betaCorrectionUpperFromLiteralDerivative {dynamics = dynamics} bounds k k<K
  rewrite betaCorrectionIsLiteralMixedDerivative dynamics k k<K =
  derivativeUpper bounds k k<K

cmp109VacuumPolarisationBetaIdentityLevel : ProofLevel
cmp109VacuumPolarisationBetaIdentityLevel = machineChecked

literalDerivativeBoundsToPointwiseBetaLevel : ProofLevel
literalDerivativeBoundsToPointwiseBetaLevel = machineChecked

-- TRUE source-facing A1 scalar leaf after this weld:
-- prove uniform two-sided bounds on the exact CMP109 mixed second derivative
-- carried by each generated finite-cutoff dynamics.  The lower bound must be
-- positive on the same admissible history/tube; the upper bound only needs to
-- be finite.  No extra beta-sequence identification is required.
literalCMP109MixedDerivativeTwoSidedBoundLevel : ProofLevel
literalCMP109MixedDerivativeTwoSidedBoundLevel = conditional
