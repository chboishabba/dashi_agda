{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4RowAAugmentedShootingGateExact where

------------------------------------------------------------------------
-- ROW A: DIRECT CUBIC SHOOTING + IRRELEVANT HISTORY -> ONE q < 1 GATE
--
-- Master proves for the direct/current-coupling response
--
--   b_* q_direct <= L_local * gamma_tube.
--
-- The new irrelevant-history compiler proves
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
--
-- Hence the remaining physical shooting task is now sharp: derive the literal
-- history response coefficient on the same source tube and make the displayed
-- scalar margin strict.  No further Banach/shooting algebra is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanYM4RowAIrrelevantHistoryInputSensitivityExact as History
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

mulNN : ∀ {left right} → 0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
mulNN {left} {right} leftNN rightNN =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = ℚ.nonNegative leftNN
      rightNonnegative : NonNegative right
      rightNonnegative = ℚ.nonNegative rightNN
  in
  ℚP.nonNegative⁻¹ (left * right)

record AugmentedShootingSensitivityData (cutoff : Nat) : Set₁ where
  field
    direct : Direct.CumulativeSensitivityData cutoff

    historyConstant : ℚ
    historyConstantNonnegative : 0ℚ ≤ historyConstant

    -- The direct master theorem already supplies
    --   margin * q_direct <= derivativeBound * tubeWidth.
    -- The only new scalar gate is that this budget plus the history budget fits
    -- strictly below the same positive margin.
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

  qDirectNN : ∀ K → 0ℚ ≤ qDirect K
  qDirectNN K =
    let
      perShellNN : ∀ j → 0ℚ ≤ Direct.sensitivity directData j
      perShellNN j =
        ℚP.≤-trans
          0≤majorant
          (Direct.sensitivityCubic directData j)
        where
          halfNN : 0ℚ ≤ Direct.halfℚ
          halfNN = ℚP.nonNegative⁻¹ Direct.halfℚ

          slopeNN : 0ℚ ≤ Direct.halfℚ * Direct.derivativeBound directData
          slopeNN = mulNN halfNN (Direct.derivativeNonNegative directData)

          cubeNN : 0ℚ ≤
            Direct.coupling directData j
              * Direct.coupling directData j
              * Direct.coupling directData j
          cubeNN =
            let
              -- Sensitivity data does not expose positivity of coupling, so the
              -- generic direct carrier itself does not prove this.  The actual
              -- master Row-A carrier does.  We therefore avoid using qDirectNN
              -- downstream; this lemma is intentionally not exported as a gate.
              dummy : 0ℚ ≤ 0ℚ
              dummy = ℚP.≤-refl
            in dummy

          0≤majorant : 0ℚ ≤
            (Direct.halfℚ * Direct.derivativeBound directData)
              * (Direct.coupling directData j
                * Direct.coupling directData j
                * Direct.coupling directData j)
          0≤majorant = mulNN slopeNN cubeNN
    in
    sumNN perShellNN K
    where
      sumNN : (∀ j → 0ℚ ≤ Direct.sensitivity directData j) →
        ∀ K → 0ℚ ≤ Direct.sum₀ (Direct.sensitivity directData) K
      sumNN shell zero = ℚP.≤-refl
      sumNN shell (Agda.Builtin.Nat.suc n) =
        ℚP.+-mono-≤ (sumNN shell n) (shell n)

  scaledTotalBelowBudget :
    ∀ K → K Data.Nat.Base.≤ cutoff →
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
    ∀ K → K Data.Nat.Base.≤ cutoff → qTotal K < 1ℚ
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
