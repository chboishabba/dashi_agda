{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanVacuumPolarisationTunedFamilyToFrozenRowAExact where

------------------------------------------------------------------------
-- ROUND101 A-CAPSTONE REDUCTION
--
-- Backward from the frozen Row-A owner, after the additive compilers have been
-- eliminated, the source-facing object is now a tuned family of ACTUAL CMP109
-- dynamics with two-sided bounds on the exact (5.42) mixed derivative.
--
-- The response-kernel/quartic-injection machinery remains a useful way to prove
-- the tuning data.  It is not an extra field of the frozen endpoint: any valid
-- source-native tuning argument may supply the same record below.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
import Data.Nat.Base as ℕ
open import Data.Product using (_×_)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _≤ℝ_; _<ℝ_)
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  (SourceAuthorityId; VerificationStatus)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory as Trajectory
import DASHI.Physics.YangMills.BalabanCutoffBetaLaw as BetaLaw
import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget as Budget
import DASHI.Physics.YangMills.BalabanPointwiseBetaBoundsToFrozenRowAExact as Pointwise
import DASHI.Physics.YangMills.BalabanVacuumPolarisationPointwiseBetaBoundsExact as VP
import DASHI.Physics.YangMills.BalabanClayFrozenFourCompletionContractExact as Frozen

record LiteralCMP109MixedDerivativeTunedFamily : Set₁ where
  field
    gamma : ℝ
    gammaPositive : 0ℝ <ℝ gamma

    bareCoupling : Nat → ℝ
    dynamics : (K : Nat) → BetaLaw.BalabanCutoffCouplingDynamics K

    startsAtBareCoupling :
      ∀ K →
      Trajectory.coupling (BetaLaw.step (dynamics K)) zero ≡ bareCoupling K

    threshold :
      ∀ K →
      Budget.InverseSquareThresholdControlsCoupling
        K gamma (BetaLaw.step (dynamics K))

    betaLower betaUpper : ℝ
    betaLowerPositive : 0ℝ <ℝ betaLower
    betaLowerBelowUpper : betaLower ≤ℝ betaUpper

    -- These are bounds on the exact CMP109 (5.42) scalar already carried by
    -- `vacuumPolarisationCoefficient`, not on a separately postulated beta law.
    mixedDerivativeLower :
      ∀ K k → k ℕ.< K →
      betaLower ≤ℝ
        BetaLaw.negativeOffDiagonalSecondMomentumDerivative
          (BetaLaw.vacuumPolarisationCoefficient (dynamics K)) k

    mixedDerivativeUpper :
      ∀ K k → k ℕ.< K →
      BetaLaw.negativeOffDiagonalSecondMomentumDerivative
        (BetaLaw.vacuumPolarisationCoefficient (dynamics K)) k
      ≤ℝ betaUpper

    -- Bare-coordinate/tuning data.  The linear beta prefix majorant is generated
    -- from `mixedDerivativeUpper`; it is not another analytic hypothesis.
    bareBudget :
      ∀ K k → k ℕ.≤ K →
      Budget.gammaInverseSquare (threshold K)
        +ℝ Pointwise.linear betaUpper k
      ≤ℝ Trajectory.inverseSquaredCoupling (BetaLaw.step (dynamics K)) zero

    renormalisedCouplingLower renormalisedCouplingUpper : ℝ
    renormalisedLowerPositive : 0ℝ <ℝ renormalisedCouplingLower
    observationScale : Nat → Nat
    observationWithinCutoff : ∀ K → observationScale K ℕ.≤ K
    terminalCouplingWindow :
      ∀ K →
      renormalisedCouplingLower ≤ℝ
        Trajectory.coupling (BetaLaw.step (dynamics K)) (observationScale K)
      ×
      Trajectory.coupling (BetaLaw.step (dynamics K)) (observationScale K)
        ≤ℝ renormalisedCouplingUpper

    terminalRenormalisationCondition : Set
    ultravioletBareCouplingSmallness : Set

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open LiteralCMP109MixedDerivativeTunedFamily public

asLiteralDerivativeBounds :
  (family : LiteralCMP109MixedDerivativeTunedFamily) →
  ∀ K → VP.LiteralVacuumPolarisationPointwiseBounds (dynamics family K)
asLiteralDerivativeBounds family K = record
  { VP.LiteralVacuumPolarisationPointwiseBounds.betaLower = betaLower family
  ; VP.LiteralVacuumPolarisationPointwiseBounds.betaUpper = betaUpper family
  ; VP.LiteralVacuumPolarisationPointwiseBounds.betaLowerPositive =
      betaLowerPositive family
  ; VP.LiteralVacuumPolarisationPointwiseBounds.betaLowerBelowUpper =
      betaLowerBelowUpper family
  ; VP.LiteralVacuumPolarisationPointwiseBounds.derivativeLower =
      mixedDerivativeLower family K
  ; VP.LiteralVacuumPolarisationPointwiseBounds.derivativeUpper =
      mixedDerivativeUpper family K
  }

asPointwiseBetaTunedFamily :
  LiteralCMP109MixedDerivativeTunedFamily → Pointwise.PointwiseBetaTunedFamily
asPointwiseBetaTunedFamily family = record
  { Pointwise.PointwiseBetaTunedFamily.gamma = gamma family
  ; Pointwise.PointwiseBetaTunedFamily.gammaPositive = gammaPositive family
  ; Pointwise.PointwiseBetaTunedFamily.bareCoupling = bareCoupling family
  ; Pointwise.PointwiseBetaTunedFamily.dynamics = dynamics family
  ; Pointwise.PointwiseBetaTunedFamily.startsAtBareCoupling =
      startsAtBareCoupling family
  ; Pointwise.PointwiseBetaTunedFamily.threshold = threshold family
  ; Pointwise.PointwiseBetaTunedFamily.betaLower = betaLower family
  ; Pointwise.PointwiseBetaTunedFamily.betaUpper = betaUpper family
  ; Pointwise.PointwiseBetaTunedFamily.betaLowerPositive = betaLowerPositive family
  ; Pointwise.PointwiseBetaTunedFamily.betaLowerBelowUpper = betaLowerBelowUpper family
  ; Pointwise.PointwiseBetaTunedFamily.pointwiseBetaLower =
      λ K k k<K →
        VP.betaCorrectionLowerFromLiteralDerivative
          (asLiteralDerivativeBounds family K) k k<K
  ; Pointwise.PointwiseBetaTunedFamily.pointwiseBetaUpper =
      λ K k k<K →
        VP.betaCorrectionUpperFromLiteralDerivative
          (asLiteralDerivativeBounds family K) k k<K
  ; Pointwise.PointwiseBetaTunedFamily.bareBudget = bareBudget family
  ; Pointwise.PointwiseBetaTunedFamily.renormalisedCouplingLower =
      renormalisedCouplingLower family
  ; Pointwise.PointwiseBetaTunedFamily.renormalisedCouplingUpper =
      renormalisedCouplingUpper family
  ; Pointwise.PointwiseBetaTunedFamily.renormalisedLowerPositive =
      renormalisedLowerPositive family
  ; Pointwise.PointwiseBetaTunedFamily.observationScale = observationScale family
  ; Pointwise.PointwiseBetaTunedFamily.observationWithinCutoff =
      observationWithinCutoff family
  ; Pointwise.PointwiseBetaTunedFamily.terminalCouplingWindow =
      terminalCouplingWindow family
  ; Pointwise.PointwiseBetaTunedFamily.terminalRenormalisationCondition =
      terminalRenormalisationCondition family
  ; Pointwise.PointwiseBetaTunedFamily.ultravioletBareCouplingSmallness =
      ultravioletBareCouplingSmallness family
  ; Pointwise.PointwiseBetaTunedFamily.sourceAuthorityId = sourceAuthorityId family
  ; Pointwise.PointwiseBetaTunedFamily.theoremLocator = theoremLocator family
  ; Pointwise.PointwiseBetaTunedFamily.status = status family
  ; Pointwise.PointwiseBetaTunedFamily.noClayPromotion = noClayPromotion family
  }

literalCMP109MixedDerivativeFamilyToFrozenRowA :
  LiteralCMP109MixedDerivativeTunedFamily →
  Frozen.LiteralCompactSimplePositiveBetaCompletion
literalCMP109MixedDerivativeFamilyToFrozenRowA family =
  Pointwise.pointwiseFrozenRowA (asPointwiseBetaTunedFamily family)

literalMixedDerivativeFamilyToFrozenRowACompilerLevel : ProofLevel
literalMixedDerivativeFamilyToFrozenRowACompilerLevel = machineChecked

-- Remaining A theorem is now source/physical rather than additive bookkeeping:
-- construct this tuned family from the literal finite-cutoff RG transformation.
-- The Ward/constrained-Gaussian and normalized-interaction estimates must bound
-- the exact (5.42) derivative uniformly over the admitted generated histories;
-- a tuning argument must also provide the nonvanishing observation window.
literalCMP109MixedDerivativeTunedFamilyLevel : ProofLevel
literalCMP109MixedDerivativeTunedFamilyLevel = conditional
