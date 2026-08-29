module DASHI.Physics.YangMills.BalabanPointwiseBetaBoundsToFrozenRowAExact where

------------------------------------------------------------------------
-- ROUND101: POINTWISE LITERAL BETA BOUNDS -> ALL ROW-A ADDITIVE LEDGERS
--
-- BIDI move:
--
--   backward: the frozen Row-A consumer asks for
--     (i) a tuned `BalabanRenormalisedCouplingConstruction`, and
--     (ii) bilateral terminal-tail bounds for the SAME generated beta history.
--
--   forward: the literal CMP109 producer naturally aims at pointwise bounds
--
--          betaLower <= betaCorrection_j <= betaUpper.
--
-- The finite prefix and arbitrary terminal-tail estimates are therefore not new
-- analytic theorems.  This file proves them by finite ordered-additive induction.
-- In particular, once the same generated dynamics has a uniform positive
-- pointwise lower beta bound and a finite pointwise upper beta bound, the
-- `betaTerminalTailBilateral` field of the frozen completion is automatic.
--
-- IMPORTANT: this does NOT construct the source beta bounds or the tuned
-- observation-scale window.  It removes duplicate cumulative estimates after
-- those literal source facts exist.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base as ℕ using (_≤_; _+_)
open import Data.Product using (_×_; _,_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _+ℝ_ ; _≤ℝ_ ; _<ℝ_
  ; ≤ℝ-refl ; +-mono-≤ )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  (SourceAuthorityId; VerificationStatus)

import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory as Trajectory
import DASHI.Physics.YangMills.BalabanCutoffBetaLaw as BetaLaw
import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget as Budget
import DASHI.Physics.YangMills.BalabanBetaPrefixEstimate as Prefix
import DASHI.Physics.YangMills.BalabanRenormalisedCouplingExistence as Renorm
import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra as Interval
import DASHI.Physics.YangMills.BalabanClayFrozenFourCompletionContractExact as Frozen
import DASHI.Physics.YangMills.CompactLieProofLevel as Level

linear : ℝ → Nat → ℝ
linear slope zero = 0ℝ
linear slope (suc n) = linear slope n +ℝ slope

linearZero : ∀ slope → linear slope zero ≡ 0ℝ
linearZero slope = refl

linearStep : ∀ slope n → linear slope (suc n) ≡ linear slope n +ℝ slope
linearStep slope n = refl

------------------------------------------------------------------------
-- Pointwise bounds generate every finite interval bound.
------------------------------------------------------------------------

intervalLowerFromPointwise :
  (beta : Nat → ℝ) (lower : ℝ) →
  (∀ j → lower ≤ℝ beta (suc j)) →
  ∀ k n →
  linear lower n ≤ℝ Interval.intervalSum beta k n
intervalLowerFromPointwise beta lower pointwise k zero = ≤ℝ-refl
intervalLowerFromPointwise beta lower pointwise k (suc n) =
  +-mono-≤
    (intervalLowerFromPointwise beta lower pointwise k n)
    (pointwise (n + k))

intervalUpperFromPointwise :
  (beta : Nat → ℝ) (upper : ℝ) →
  (∀ j → beta (suc j) ≤ℝ upper) →
  ∀ k n →
  Interval.intervalSum beta k n ≤ℝ linear upper n
intervalUpperFromPointwise beta upper pointwise k zero = ≤ℝ-refl
intervalUpperFromPointwise beta upper pointwise k (suc n) =
  +-mono-≤
    (intervalUpperFromPointwise beta upper pointwise k n)
    (pointwise (n + k))

prefixUpperFromPointwise :
  (step : Trajectory.BalabanInverseSquareCouplingStep)
  (upper : ℝ) →
  (∀ j → Trajectory.betaCorrection step (suc j) ≤ℝ upper) →
  ∀ k →
  Budget.betaPrefixSum step k ≤ℝ linear upper k
prefixUpperFromPointwise step upper pointwise zero = ≤ℝ-refl
prefixUpperFromPointwise step upper pointwise (suc k) =
  +-mono-≤
    (prefixUpperFromPointwise step upper pointwise k)
    (pointwise k)

------------------------------------------------------------------------
-- Minimal data before the old prefix-estimate wrapper.
--
-- This is deliberately weaker than `BalabanRenormalisedCouplingConstruction`:
-- it does NOT ask for `actualPrefixEstimate`.  Pointwise upper beta control plus
-- the bare inverse-square budget constructs that field below.
------------------------------------------------------------------------

record PointwiseBetaTunedFamily : Set₁ where
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

    pointwiseBetaLower :
      ∀ K j →
      betaLower ≤ℝ
        Trajectory.betaCorrection (BetaLaw.step (dynamics K)) (suc j)

    pointwiseBetaUpper :
      ∀ K j →
      Trajectory.betaCorrection (BetaLaw.step (dynamics K)) (suc j)
        ≤ℝ betaUpper

    -- This is the actual tuning/bare-coordinate input.  The prefix majorant is
    -- fixed here to the linear upper envelope generated above, so no second
    -- analytic prefix estimate remains.
    bareBudget :
      ∀ K k → k ≤ K →
      Budget.gammaInverseSquare (threshold K) +ℝ linear betaUpper k
        ≤ℝ Trajectory.inverseSquaredCoupling (BetaLaw.step (dynamics K)) zero

    renormalisedCouplingLower renormalisedCouplingUpper : ℝ
    renormalisedLowerPositive : 0ℝ <ℝ renormalisedCouplingLower
    observationScale : Nat → Nat
    observationWithinCutoff : ∀ K → observationScale K ≤ K
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

open PointwiseBetaTunedFamily public

pointwisePrefixBudget :
  (family : PointwiseBetaTunedFamily) →
  ∀ K →
  Budget.BalabanBetaPrefixBound
    K (BetaLaw.step (dynamics family K)) (threshold family K)
pointwisePrefixBudget family K = record
  { Budget.BalabanBetaPrefixBound.prefixMajorant = linear (betaUpper family)
  ; Budget.BalabanBetaPrefixBound.betaPrefixControlled =
      λ k k≤K → prefixUpperFromPointwise
        (BetaLaw.step (dynamics family K))
        (betaUpper family)
        (pointwiseBetaUpper family K)
        k
  ; Budget.BalabanBetaPrefixBound.bareCouplingBudget = bareBudget family K
  ; Budget.BalabanBetaPrefixBound.sourceAuthorityId = sourceAuthorityId family
  ; Budget.BalabanBetaPrefixBound.theoremLocator = theoremLocator family
  ; Budget.BalabanBetaPrefixBound.status = status family
  ; Budget.BalabanBetaPrefixBound.noClayPromotion = noClayPromotion family
  }

pointwiseActualPrefixEstimate :
  (family : PointwiseBetaTunedFamily) →
  ∀ K →
  Prefix.BalabanActualBetaPrefixEstimate
    K (dynamics family K) (threshold family K)
pointwiseActualPrefixEstimate family K = record
  { Prefix.BalabanActualBetaPrefixEstimate.prefixBudget =
      pointwisePrefixBudget family K
  ; Prefix.BalabanActualBetaPrefixEstimate.sourceAuthorityId = sourceAuthorityId family
  ; Prefix.BalabanActualBetaPrefixEstimate.theoremLocator = theoremLocator family
  ; Prefix.BalabanActualBetaPrefixEstimate.status = status family
  ; Prefix.BalabanActualBetaPrefixEstimate.noClayPromotion = noClayPromotion family
  }

pointwiseRenormalisedConstruction :
  PointwiseBetaTunedFamily → Renorm.BalabanRenormalisedCouplingConstruction
pointwiseRenormalisedConstruction family = record
  { Renorm.BalabanRenormalisedCouplingConstruction.γ = gamma family
  ; Renorm.BalabanRenormalisedCouplingConstruction.γ-positive = gammaPositive family
  ; Renorm.BalabanRenormalisedCouplingConstruction.bareCoupling = bareCoupling family
  ; Renorm.BalabanRenormalisedCouplingConstruction.dynamics = dynamics family
  ; Renorm.BalabanRenormalisedCouplingConstruction.startsAtBareCoupling =
      startsAtBareCoupling family
  ; Renorm.BalabanRenormalisedCouplingConstruction.threshold = threshold family
  ; Renorm.BalabanRenormalisedCouplingConstruction.actualPrefixEstimate =
      pointwiseActualPrefixEstimate family
  ; Renorm.BalabanRenormalisedCouplingConstruction.renormalisedCouplingLower =
      renormalisedCouplingLower family
  ; Renorm.BalabanRenormalisedCouplingConstruction.renormalisedCouplingUpper =
      renormalisedCouplingUpper family
  ; Renorm.BalabanRenormalisedCouplingConstruction.lowerPositive =
      renormalisedLowerPositive family
  ; Renorm.BalabanRenormalisedCouplingConstruction.observationScale = observationScale family
  ; Renorm.BalabanRenormalisedCouplingConstruction.observationWithinCutoff =
      observationWithinCutoff family
  ; Renorm.BalabanRenormalisedCouplingConstruction.terminalCouplingWindow =
      terminalCouplingWindow family
  ; Renorm.BalabanRenormalisedCouplingConstruction.terminalRenormalisationCondition =
      terminalRenormalisationCondition family
  ; Renorm.BalabanRenormalisedCouplingConstruction.ultravioletBareCouplingSmallness =
      ultravioletBareCouplingSmallness family
  ; Renorm.BalabanRenormalisedCouplingConstruction.sourceAuthorityId = sourceAuthorityId family
  ; Renorm.BalabanRenormalisedCouplingConstruction.theoremLocator = theoremLocator family
  ; Renorm.BalabanRenormalisedCouplingConstruction.status = status family
  ; Renorm.BalabanRenormalisedCouplingConstruction.noClayPromotion = noClayPromotion family
  }

pointwiseFrozenRowA :
  PointwiseBetaTunedFamily → Frozen.LiteralCompactSimplePositiveBetaCompletion
pointwiseFrozenRowA family = record
  { Frozen.LiteralCompactSimplePositiveBetaCompletion.construction =
      pointwiseRenormalisedConstruction family
  ; Frozen.LiteralCompactSimplePositiveBetaCompletion.lowerSlope = betaLower family
  ; Frozen.LiteralCompactSimplePositiveBetaCompletion.upperSlope = betaUpper family
  ; Frozen.LiteralCompactSimplePositiveBetaCompletion.lowerSlopePositive =
      betaLowerPositive family
  ; Frozen.LiteralCompactSimplePositiveBetaCompletion.lowerSlopeBelowUpperSlope =
      betaLowerBelowUpper family
  ; Frozen.LiteralCompactSimplePositiveBetaCompletion.lowerLinear = linear (betaLower family)
  ; Frozen.LiteralCompactSimplePositiveBetaCompletion.upperLinear = linear (betaUpper family)
  ; Frozen.LiteralCompactSimplePositiveBetaCompletion.lowerLinearZero = refl
  ; Frozen.LiteralCompactSimplePositiveBetaCompletion.upperLinearZero = refl
  ; Frozen.LiteralCompactSimplePositiveBetaCompletion.lowerLinearStep = λ n → refl
  ; Frozen.LiteralCompactSimplePositiveBetaCompletion.upperLinearStep = λ n → refl
  ; Frozen.LiteralCompactSimplePositiveBetaCompletion.betaTerminalTailBilateral =
      λ K k n k+n≡K →
        intervalLowerFromPointwise
          (Trajectory.betaCorrection (BetaLaw.step (dynamics family K)))
          (betaLower family)
          (pointwiseBetaLower family K)
          k n
        ,
        intervalUpperFromPointwise
          (Trajectory.betaCorrection (BetaLaw.step (dynamics family K)))
          (betaUpper family)
          (pointwiseBetaUpper family K)
          k n
  }

pointwiseBetaBoundsToPrefixLevel : Level.ProofLevel
pointwiseBetaBoundsToPrefixLevel = Level.machineChecked

pointwiseBetaBoundsToFrozenRowACompilerLevel : Level.ProofLevel
pointwiseBetaBoundsToFrozenRowACompilerLevel = Level.machineChecked

-- Remaining physical source facts on this shortest route are now exactly:
--   * actual CMP109 generated dynamics;
--   * uniform literal pointwise betaLower/betaUpper on those dynamics;
--   * the tuned bare/observation window and its threshold coordinate meaning.
-- Prefix summation and frozen terminal-tail bilaterality are downstream.
literalPointwiseBetaTunedFamilyLevel : Level.ProofLevel
literalPointwiseBetaTunedFamilyLevel = Level.conditional
