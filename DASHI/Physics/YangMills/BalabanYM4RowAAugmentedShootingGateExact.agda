{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4RowAAugmentedShootingGateExact where

------------------------------------------------------------------------
-- ROW A: DIRECT CUBIC SHOOTING + IRRELEVANT HISTORY -> ONE q < 1 GATE
--
-- Master proves for the direct/current-coupling response
--
--   b_* q_direct <= L_local * gamma_tube.
--
-- The irrelevant-history compiler proves separately
--
--   |delta B_history| <= q_history |delta u|.
--
-- This file combines the two WITHOUT pretending that the marginal coupling
-- forgets exponentially.  The exact division-free augmented gate is
--
--   L_local * gamma_tube + b_* q_history < b_*.
--
-- From it we prove
--
--   q_direct + q_history < 1.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct

record AugmentedShootingSensitivityData (cutoff : Nat) : Set₁ where
  field
    direct : Direct.CumulativeSensitivityData cutoff

    historyConstant : ℚ
    historyConstantNonnegative : 0ℚ ≤ historyConstant

    -- The direct theorem supplies
    --   margin * q_direct <= derivativeBound * tubeWidth.
    -- This one scalar strict inequality fits that direct budget and the
    -- independently-derived irrelevant-history Lipschitz budget below the same
    -- positive beta margin.
    augmentedContractionGate :
      Direct.derivativeBound direct * Direct.tubeWidth direct
        + Direct.marginConstant direct * historyConstant
      < Direct.marginConstant direct

open AugmentedShootingSensitivityData public

module Augmented {cutoff : Nat}
    (dataSet : AugmentedShootingSensitivityData cutoff) where

  directData : Direct.CumulativeSensitivityData cutoff
  directData = direct dataSet

  module D = Direct.Sensitivity directData

  qDirect : Nat → ℚ
  qDirect K = Direct.sum₀ (Direct.sensitivity directData) K

  qHistory : ℚ
  qHistory = historyConstant dataSet

  qTotal : Nat → ℚ
  qTotal K = qDirect K + qHistory

  marginNN : 0ℚ ≤ Direct.marginConstant directData
  marginNN = ℚP.<⇒≤ (Direct.marginPositive directData)

  scaledTotalBelowBudget :
    ∀ K → K ℕ.≤ cutoff →
    Direct.marginConstant directData * qTotal K
    ≤ Direct.derivativeBound directData * Direct.tubeWidth directData
      + Direct.marginConstant directData * qHistory
  scaledTotalBelowBudget K K≤ =
    let
      directBound = D.scaledCumulativeSensitivity K K≤
      historyRefl :
        Direct.marginConstant directData * qHistory
        ≤ Direct.marginConstant directData * qHistory
      historyRefl = ℚP.≤-refl
      added = ℚP.+-mono-≤ directBound historyRefl
    in
    subst
      (λ left → left ≤
        Direct.derivativeBound directData * Direct.tubeWidth directData
          + Direct.marginConstant directData * qHistory)
      (ℚRing.solve-∀
        (Direct.marginConstant directData)
        (qDirect K) qHistory)
      added

  qTotalBelowOne :
    ∀ K → K ℕ.≤ cutoff → qTotal K < 1ℚ
  qTotalBelowOne K K≤ =
    let
      scaled = scaledTotalBelowBudget K K≤
      strictScaled :
        Direct.marginConstant directData * qTotal K
        < Direct.marginConstant directData
      strictScaled = ℚP.≤-<-trans scaled (augmentedContractionGate dataSet)
    in
    ℚP.*-cancelˡ-<-nonNeg
      (Direct.marginConstant directData)
      {{ℚ.nonNegative marginNN}}
      (subst
        (λ right → Direct.marginConstant directData * qTotal K < right)
        (sym (ℚP.*-identityʳ (Direct.marginConstant directData)))
        strictScaled)

rowAAugmentedShootingBudgetAlgebraLevel : ProofLevel
rowAAugmentedShootingBudgetAlgebraLevel = machineChecked

rowAAugmentedShootingSubunitLevel : ProofLevel
rowAAugmentedShootingSubunitLevel = machineChecked

-- Physical seam: instantiate q_history from the literal irrelevant/polymer
-- response to the initial inverse-square shooting input and prove
--
--   L_local gamma_tube + b_* q_history < b_*
--
-- on the SAME generated trajectory.  This is the honest total-sensitivity gate.
literalRowAAugmentedHistoryGateLevel : ProofLevel
literalRowAAugmentedHistoryGateLevel = conditional
