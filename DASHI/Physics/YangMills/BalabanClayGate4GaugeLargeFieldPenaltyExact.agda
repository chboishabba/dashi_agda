module DASHI.Physics.YangMills.BalabanClayGate4GaugeLargeFieldPenaltyExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4DimockLargeFieldSuppressionExact as LargeField

------------------------------------------------------------------------
-- Yang--Mills bad-block criterion and action-penalty ownership.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban. II. Large Fields",
-- Journal of Mathematical Physics 54 (9) (2013), article 092301.
-- arXiv:1212.5562v2. DOI: 10.1063/1.4821275.
--
-- A physical bad cube must be tied to a literal small-field failure, for example
-- a plaquette defect or chart C^1 threshold.  The Wilson action must then pay a
-- one-cube coercive penalty.  This adapter identifies that penalty with the
-- generic entropy-plus-reserved-slack budget already proved for arbitrary
-- finite bad regions.
------------------------------------------------------------------------

record GaugeBadBlockCriterion
    (Block Configuration Scalar : Set) : Set₁ where
  field
    plaquetteDefect chartDerivativeSize threshold :
      Block → Configuration → Scalar

    LessEqual : Scalar → Scalar → Set

    PlaquetteBad ChartBad Bad : Block → Configuration → Set

    plaquetteBadMeaning : ∀ block configuration →
      PlaquetteBad block configuration
      ≡ LessEqual threshold
          (plaquetteDefect block configuration)

    chartBadMeaning : ∀ block configuration →
      ChartBad block configuration
      ≡ LessEqual threshold
          (chartDerivativeSize block configuration)

    badIsPlaquetteOrChart : ∀ block configuration →
      Bad block configuration →
      Set

open GaugeBadBlockCriterion public

record GaugeLargeFieldPenaltyInputs
    (Scale Block Configuration Scalar : Set) : Set₁ where
  field
    criterionAt : Scale →
      GaugeBadBlockCriterion Block Configuration Scalar

    localWilsonAction : Scale → Block → Configuration → Scalar
    localPenalty : Scale → Scalar

    LocalActionPenaltyMeaning : Set
    localActionPenaltyMeaning : LocalActionPenaltyMeaning

    badBlockPaysPenalty : ∀ scale block configuration →
      Bad (criterionAt scale) block configuration →
      LessEqual (criterionAt scale)
        (localPenalty scale)
        (localWilsonAction scale block configuration)

    multiscaleBudget :
      LargeField.MultiscaleLargeFieldBudget Scale Scalar

    penaltyMatchesBudget : ∀ scale →
      localPenalty scale
      ≡ LargeField.penaltyPerBadCube
          (LargeField.budgetAt multiscaleBudget scale)

open GaugeLargeFieldPenaltyInputs public

gaugeBadRegionPaysEntropyAndSlack :
  ∀ {Scale Block Configuration Scalar}
    (inputs : GaugeLargeFieldPenaltyInputs
      Scale Block Configuration Scalar)
    scale →
  LargeField.LessEqual
    (LargeField.algebra
      (LargeField.budgetAt (multiscaleBudget inputs) scale))
    (LargeField.natScale
      (LargeField.algebra
        (LargeField.budgetAt (multiscaleBudget inputs) scale))
      (LargeField.add
        (LargeField.algebra
          (LargeField.budgetAt (multiscaleBudget inputs) scale))
        (LargeField.entropyPerBadCube
          (LargeField.budgetAt (multiscaleBudget inputs) scale))
        (LargeField.reservedSlackPerBadCube
          (LargeField.budgetAt (multiscaleBudget inputs) scale)))
      (LargeField.badCubeCountAt (multiscaleBudget inputs) scale))
    (LargeField.natScale
      (LargeField.algebra
        (LargeField.budgetAt (multiscaleBudget inputs) scale))
      (LargeField.penaltyPerBadCube
        (LargeField.budgetAt (multiscaleBudget inputs) scale))
      (LargeField.badCubeCountAt (multiscaleBudget inputs) scale))
gaugeBadRegionPaysEntropyAndSlack inputs =
  LargeField.multiscaleLargeFieldSlackAt (multiscaleBudget inputs)

gaugeBadBlockCriterionLevel : ProofLevel
gaugeBadBlockCriterionLevel = machineChecked

gaugeLargeFieldBudgetReuseLevel : ProofLevel
gaugeLargeFieldBudgetReuseLevel = machineChecked

physicalWilsonPlaquettePenaltyInputsLevel : ProofLevel
physicalWilsonPlaquettePenaltyInputsLevel = conditional

physicalGaugeBadRegionEntropyInputsLevel : ProofLevel
physicalGaugeBadRegionEntropyInputsLevel = conditional
