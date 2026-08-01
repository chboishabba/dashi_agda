module DASHI.Physics.YangMills.BalabanClayGate4DimockLargeFieldSuppressionExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Additive exponent budget for Dimock II/III large-field suppression.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban - II. Large Fields",
-- arXiv:1212.5562v2 [math-ph]. No DOI recorded.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban - III. Convergence",
-- arXiv:1304.0705v1 [math-ph]. No DOI recorded.
--
-- On every bad cube at least one small-field inequality fails and the action
-- supplies a penalty of order p_k^2.  The sum over possible bad regions has an
-- entropy cost.  The usable statement is not merely "large fields are small":
-- one reserves an explicit positive slack after paying that entropy.  The
-- finite theorem below scales the one-cube inequality to every finite bad-cube
-- count.
------------------------------------------------------------------------

record OrderedAdditiveBudget (Scalar : Set) : Set₁ where
  field
    zero : Scalar
    add : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (add left right) (add lower upper)

open OrderedAdditiveBudget public

natScale :
  ∀ {Scalar} → OrderedAdditiveBudget Scalar → Scalar → Nat → Scalar
natScale algebra value zero = zero algebra
natScale algebra value (suc count) =
  add algebra value (natScale algebra value count)

natScaleMonotone :
  ∀ {Scalar}
    (algebra : OrderedAdditiveBudget Scalar)
    {lower upper} →
  LessEqual algebra lower upper →
  ∀ count →
  LessEqual algebra
    (natScale algebra lower count)
    (natScale algebra upper count)
natScaleMonotone algebra estimate zero =
  reflexive algebra (zero algebra)
natScaleMonotone algebra estimate (suc count) =
  addMonotone algebra estimate
    (natScaleMonotone algebra estimate count)

record LargeFieldCubeBudget (Scalar : Set) : Set₁ where
  field
    algebra : OrderedAdditiveBudget Scalar
    entropyPerBadCube reservedSlackPerBadCube penaltyPerBadCube : Scalar

    penaltyPaysEntropyAndSlack :
      LessEqual algebra
        (add algebra entropyPerBadCube reservedSlackPerBadCube)
        penaltyPerBadCube

open LargeFieldCubeBudget public

largeFieldPenaltyPaysFiniteEntropyAndSlack :
  ∀ {Scalar}
    (budget : LargeFieldCubeBudget Scalar)
    badCubeCount →
  LessEqual (algebra budget)
    (natScale (algebra budget)
      (add (algebra budget)
        (entropyPerBadCube budget)
        (reservedSlackPerBadCube budget))
      badCubeCount)
    (natScale (algebra budget)
      (penaltyPerBadCube budget)
      badCubeCount)
largeFieldPenaltyPaysFiniteEntropyAndSlack budget =
  natScaleMonotone (algebra budget)
    (penaltyPaysEntropyAndSlack budget)

record MultiscaleLargeFieldBudget
    (Scale Scalar : Set) : Set₁ where
  field
    budgetAt : Scale → LargeFieldCubeBudget Scalar
    badCubeCountAt : Scale → Nat

open MultiscaleLargeFieldBudget public

multiscaleLargeFieldSlackAt :
  ∀ {Scale Scalar}
    (dataSet : MultiscaleLargeFieldBudget Scale Scalar)
    scale →
  LessEqual (algebra (budgetAt dataSet scale))
    (natScale (algebra (budgetAt dataSet scale))
      (add (algebra (budgetAt dataSet scale))
        (entropyPerBadCube (budgetAt dataSet scale))
        (reservedSlackPerBadCube (budgetAt dataSet scale)))
      (badCubeCountAt dataSet scale))
    (natScale (algebra (budgetAt dataSet scale))
      (penaltyPerBadCube (budgetAt dataSet scale))
      (badCubeCountAt dataSet scale))
multiscaleLargeFieldSlackAt dataSet scale =
  largeFieldPenaltyPaysFiniteEntropyAndSlack
    (budgetAt dataSet scale)
    (badCubeCountAt dataSet scale)

dimockFiniteLargeFieldSlackLevel : ProofLevel
dimockFiniteLargeFieldSlackLevel = machineChecked

dimockLargeFieldSuppressionSourceLevel : ProofLevel
dimockLargeFieldSuppressionSourceLevel = standardImported

physicalYangMillsBadCubePenaltyInputsLevel : ProofLevel
physicalYangMillsBadCubePenaltyInputsLevel = conditional

physicalYangMillsLargeFieldEntropyInputsLevel : ProofLevel
physicalYangMillsLargeFieldEntropyInputsLevel = conditional
