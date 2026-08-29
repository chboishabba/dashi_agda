{-# OPTIONS --safe #-}
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
--          betaLower <= betaCorrection_(j+1) <= betaUpper,    j < K.
--
-- The finite prefix and terminal-tail estimates are therefore not new analytic
-- theorems.  This file derives them by exact finite ordered-additive induction.
-- The pointwise premise is required ONLY on the physical shells `suc j <= K`;
-- the total-function extension of `betaCorrection` beyond the cutoff is never
-- constrained.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base as ℕ using (_≤_; _+_; z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

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

nat≤Trans : ∀ {a b c : Nat} → a ≤ b → b ≤ c → a ≤ c
nat≤Trans z≤n _ = z≤n
nat≤Trans (s≤s ab) (s≤s bc) = s≤s (nat≤Trans ab bc)

natPred≤Suc : ∀ n → n ≤ suc n
natPred≤Suc zero = z≤n
natPred≤Suc (suc n) = s≤s (natPred≤Suc n)

addRightSuc : ∀ a b → a + suc b ≡ suc (a + b)
addRightSuc zero b = refl
addRightSuc (suc a) b = cong suc (addRightSuc a b)

addRightZero : ∀ a → a + zero ≡ a
addRightZero zero = refl
addRightZero (suc a) = cong suc (addRightZero a)

addComm : ∀ a b → a + b ≡ b + a
addComm zero b = sym (addRightZero b)
addComm (suc a) b =
  trans (cong suc (addComm a b)) (sym (addRightSuc b a))

addRightMonoSucc : ∀ a b → a + b ≤ a + suc b
addRightMonoSucc zero b = natPred≤Suc b
addRightMonoSucc (suc a) b = s≤s (addRightMonoSucc a b)

currentShellWithin :
  ∀ {K} k n → k + suc n ≤ K → suc (n + k) ≤ K
currentShellWithin {K} k n endWithin =
  subst
    (λ index → index ≤ K)
    (trans (addRightSuc k n) (cong suc (addComm k n)))
    endWithin

previousIntervalWithin :
  ∀ {K} k n → k + suc n ≤ K → k + n ≤ K
previousIntervalWithin k n endWithin =
  nat≤Trans (addRightMonoSucc k n) endWithin

linear : ℝ → Nat → ℝ
linear slope zero = 0ℝ
linear slope (suc n) = linear slope n +ℝ slope

intervalLowerFromPointwise :
  (K : Nat) (beta : Nat → ℝ) (lower : ℝ) →
  (∀ j → suc j ≤ K → lower ≤ℝ beta (suc j)) →
  ∀ k n → k + n ≤ K →
  linear lower n ≤ℝ Interval.intervalSum beta k n
intervalLowerFromPointwise K beta lower pointwise k zero inside = ≤ℝ-refl
intervalLowerFromPointwise K beta lower pointwise k (suc n) inside =
  +-mono-≤
    (intervalLowerFromPointwise K beta lower pointwise k n
      (previousIntervalWithin k n inside))
    (pointwise (n + k) (currentShellWithin k n inside))

intervalUpperFromPointwise :
  (K : Nat) (beta : Nat → ℝ) (upper : ℝ) →
  (∀ j → suc j ≤ K → beta (suc j) ≤ℝ upper) →
  ∀ k n → k + n ≤ K →
  Interval.intervalSum beta k n ≤ℝ linear upper n
intervalUpperFromPointwise K beta upper pointwise k zero inside = ≤ℝ-refl
intervalUpperFromPointwise K beta upper pointwise k (suc n) inside =
  +-mono-≤
    (intervalUpperFromPointwise K beta upper pointwise k n
      (previousIntervalWithin k n inside))
    (pointwise (n + k) (currentShellWithin k n inside))

prefixUpperFromPointwise :
  (K : Nat)
  (step : Trajectory.BalabanInverseSquareCouplingStep)
  (upper : ℝ) →
  (∀ j → suc j ≤ K →
    Trajectory.betaCorrection step (suc j) ≤ℝ upper) →
  ∀ k → k ≤ K →
  Budget.betaPrefixSum step k ≤ℝ linear upper k
prefixUpperFromPointwise K step upper pointwise zero k≤K = ≤ℝ-refl
prefixUpperFromPointwise K step upper pointwise (suc k) sk≤K =
  +-mono-≤
    (prefixUpperFromPointwise K step upper pointwise k
      (nat≤Trans (natPred≤Suc k) sk≤K))
    (pointwise k sk≤K)

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
      ∀ K j → suc j ≤ K →
      betaLower ≤ℝ
        Trajectory.betaCorrection (BetaLaw.step (dynamics K)) (suc j)

    pointwiseBetaUpper :
      ∀ K j → suc j ≤ K →
      Trajectory.betaCorrection (BetaLaw.step (dynamics K)) (suc j)
        ≤ℝ betaUpper

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
        K
        (BetaLaw.step (dynamics family K))
        (betaUpper family)
        (pointwiseBetaUpper family K)
        k k≤K
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
        let
          inside : k + n ≤ K
          inside = subst (λ endpoint → endpoint ≤ K) (sym k+n≡K) ℕ.≤-refl
        in
        intervalLowerFromPointwise
          K
          (Trajectory.betaCorrection (BetaLaw.step (dynamics family K)))
          (betaLower family)
          (pointwiseBetaLower family K)
          k n inside
        ,
        intervalUpperFromPointwise
          K
          (Trajectory.betaCorrection (BetaLaw.step (dynamics family K)))
          (betaUpper family)
          (pointwiseBetaUpper family K)
          k n inside
  }

pointwiseBetaBoundsToPrefixLevel : Level.ProofLevel
pointwiseBetaBoundsToPrefixLevel = Level.machineChecked

pointwiseBetaBoundsToFrozenRowACompilerLevel : Level.ProofLevel
pointwiseBetaBoundsToFrozenRowACompilerLevel = Level.machineChecked

-- Remaining physical source facts on this shortest route are exactly:
--   * actual CMP109 generated dynamics;
--   * uniform pointwise two-sided beta bounds on shells j<K;
--   * tuned bare/observation window and threshold coordinate meaning.
-- Prefix summation and frozen terminal-tail bilaterality are downstream.
literalPointwiseBetaTunedFamilyLevel : Level.ProofLevel
literalPointwiseBetaTunedFamilyLevel = Level.conditional
