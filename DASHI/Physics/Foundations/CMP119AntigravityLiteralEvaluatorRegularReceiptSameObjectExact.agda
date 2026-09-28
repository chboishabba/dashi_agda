{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLiteralEvaluatorRegularReceiptSameObjectExact where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Boxes
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4LiteralMomentumDiagramBoxDataExact as Momentum
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Literal
import DASHI.Physics.YangMills.BalabanLiteralOneLoopFourOrbitSameObjectExact as SameObject
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- LITERAL EVALUATOR -> CONFIGURED REGULAR RECEIPTS IS THE SAME FINITE OBJECT
--
-- Follow the repository's existing exact adapter chain:
--
--   LiteralGeneratedBoxEvaluator
--     -> RationalBoxEvaluator
--     -> GeneratedBrillouinPartition
--     -> RationalBrillouinBoxPartition
--     -> regularBoxReceipts.
--
-- The lower/upper receipt folds are definitionally the same rational sums as
-- `literalRegularLowerSum` / `literalRegularUpperSum` used by the four-orbit
-- same-object theorem.
------------------------------------------------------------------------

literalEvaluatorPartition :
  ∀ {expressions ward scalarData} →
  Literal.LiteralGeneratedBoxEvaluator expressions ward scalarData →
  Boxes.RationalBrillouinBoxPartition
literalEvaluatorPartition evaluator =
  Momentum.asRationalBrillouinBoxPartition
    (Grid.asGeneratedBrillouinPartition
      (Literal.asRationalBoxEvaluator evaluator))

literalEvaluatorRegularLowerReceiptSumExact :
  ∀ {expressions ward scalarData}
    (evaluator : Literal.LiteralGeneratedBoxEvaluator expressions ward scalarData) →
  Integral.boxLowerSum
    (Boxes.regularBoxReceipts (literalEvaluatorPartition evaluator))
  ≡ SameObject.literalRegularLowerSum evaluator
literalEvaluatorRegularLowerReceiptSumExact evaluator = refl

literalEvaluatorRegularUpperReceiptSumExact :
  ∀ {expressions ward scalarData}
    (evaluator : Literal.LiteralGeneratedBoxEvaluator expressions ward scalarData) →
  Integral.boxUpperSum
    (Boxes.regularBoxReceipts (literalEvaluatorPartition evaluator))
  ≡ SameObject.literalRegularUpperSum evaluator
literalEvaluatorRegularUpperReceiptSumExact evaluator = refl

literalEvaluatorRegularLowerFourOrbitExact :
  ∀ {expressions ward scalarData}
    (evaluator : Literal.LiteralGeneratedBoxEvaluator expressions ward scalarData) →
  Integral.boxLowerSum
    (Boxes.regularBoxReceipts (literalEvaluatorPartition evaluator))
  ≡
    DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact.oneOuterOrbitSum
      (SameObject.literalLowerContribution evaluator)
    + DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact.twoOuterOrbitSum
      (SameObject.literalLowerContribution evaluator)
    + DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact.threeOuterOrbitSum
      (SameObject.literalLowerContribution evaluator)
    + DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact.fourOuterOrbitSum
      (SameObject.literalLowerContribution evaluator)
literalEvaluatorRegularLowerFourOrbitExact evaluator =
  Relation.Binary.PropositionalEquality.trans
    (literalEvaluatorRegularLowerReceiptSumExact evaluator)
    (SameObject.literalLowerSumIsFourJointOrbits evaluator)

literalEvaluatorRegularUpperFourOrbitExact :
  ∀ {expressions ward scalarData}
    (evaluator : Literal.LiteralGeneratedBoxEvaluator expressions ward scalarData) →
  Integral.boxUpperSum
    (Boxes.regularBoxReceipts (literalEvaluatorPartition evaluator))
  ≡
    DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact.oneOuterOrbitSum
      (SameObject.literalUpperContribution evaluator)
    + DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact.twoOuterOrbitSum
      (SameObject.literalUpperContribution evaluator)
    + DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact.threeOuterOrbitSum
      (SameObject.literalUpperContribution evaluator)
    + DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact.fourOuterOrbitSum
      (SameObject.literalUpperContribution evaluator)
literalEvaluatorRegularUpperFourOrbitExact evaluator =
  Relation.Binary.PropositionalEquality.trans
    (literalEvaluatorRegularUpperReceiptSumExact evaluator)
    (SameObject.literalUpperSumIsFourJointOrbits evaluator)

literalEvaluatorConfiguredReceiptSameObjectLevel : ProofLevel
literalEvaluatorConfiguredReceiptSameObjectLevel = machineChecked
