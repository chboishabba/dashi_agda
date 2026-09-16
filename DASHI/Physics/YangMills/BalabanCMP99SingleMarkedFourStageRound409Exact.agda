module DASHI.Physics.YangMills.BalabanCMP99SingleMarkedFourStageRound409Exact where

------------------------------------------------------------------------
-- ROUND409 / ONE CMP99-MARKED STAGE -> WHOLE FOUR-STAGE CMP109 ENTRY
--
-- R407 owns the literal four-stage CMP109 derivative-entry carrier and all
-- ordinary before/after norm bounds.  R408 derives the genuinely changed-stage
-- marked norm estimate from the existing resolvent-defect compiler and proves
-- that a literally unchanged stage has exact zero marked cost.
--
-- R409 pays the remaining finite factor assembly without introducing a new
-- analytic estimate.  Exactly one of the four stages is designated as the
-- CMP99-marked change; the other three are accompanied by exact operator
-- equalities.  The existing noncommutative Round72 theorem then produces the
-- whole four-stage product-difference majorant.
--
-- What remains after R409 is no longer a factorwise inequality.  It is the
-- source/same-object attachment choosing which literal R407 stage is the CMP99
-- defect, proving the other three stage identities on that source object, and
-- welding this exact four-stage product difference to the selected R406 scalar
-- differentiated term.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact as Marked
import DASHI.Physics.YangMills.BalabanCMP109FourStageOperatorFactorRound407Exact as R407
import DASHI.Physics.YangMills.BalabanCMP99MarkedStageDifferenceRound408Exact as R408

------------------------------------------------------------------------
-- Exhaustive single-changed-stage attachment.
------------------------------------------------------------------------

data SingleChangedFourStageAgreement
    {Operator Bound : Set}
    (dataSet : R408.CMP99MarkedR407StageDifference Operator Bound) : Set where

  changedOuterDexp :
    R408.changedStage dataSet ≡ R407.outerDexpStage →
    R407.stageOperator (R407.before (R408.ordinaryPair dataSet))
        R407.logarithmDexpInverseStage
      ≡
    R407.stageOperator (R407.after (R408.ordinaryPair dataSet))
        R407.logarithmDexpInverseStage →
    R407.stageOperator (R407.before (R408.ordinaryPair dataSet))
        R407.transportDerivativeStage
      ≡
    R407.stageOperator (R407.after (R408.ordinaryPair dataSet))
        R407.transportDerivativeStage →
    R407.stageOperator (R407.before (R408.ordinaryPair dataSet))
        R407.pathDerivativeStage
      ≡
    R407.stageOperator (R407.after (R408.ordinaryPair dataSet))
        R407.pathDerivativeStage →
    SingleChangedFourStageAgreement dataSet

  changedLogarithmDexpInverse :
    R408.changedStage dataSet ≡ R407.logarithmDexpInverseStage →
    R407.stageOperator (R407.before (R408.ordinaryPair dataSet))
        R407.outerDexpStage
      ≡
    R407.stageOperator (R407.after (R408.ordinaryPair dataSet))
        R407.outerDexpStage →
    R407.stageOperator (R407.before (R408.ordinaryPair dataSet))
        R407.transportDerivativeStage
      ≡
    R407.stageOperator (R407.after (R408.ordinaryPair dataSet))
        R407.transportDerivativeStage →
    R407.stageOperator (R407.before (R408.ordinaryPair dataSet))
        R407.pathDerivativeStage
      ≡
    R407.stageOperator (R407.after (R408.ordinaryPair dataSet))
        R407.pathDerivativeStage →
    SingleChangedFourStageAgreement dataSet

  changedTransportDerivative :
    R408.changedStage dataSet ≡ R407.transportDerivativeStage →
    R407.stageOperator (R407.before (R408.ordinaryPair dataSet))
        R407.outerDexpStage
      ≡
    R407.stageOperator (R407.after (R408.ordinaryPair dataSet))
        R407.outerDexpStage →
    R407.stageOperator (R407.before (R408.ordinaryPair dataSet))
        R407.logarithmDexpInverseStage
      ≡
    R407.stageOperator (R407.after (R408.ordinaryPair dataSet))
        R407.logarithmDexpInverseStage →
    R407.stageOperator (R407.before (R408.ordinaryPair dataSet))
        R407.pathDerivativeStage
      ≡
    R407.stageOperator (R407.after (R408.ordinaryPair dataSet))
        R407.pathDerivativeStage →
    SingleChangedFourStageAgreement dataSet

  changedPathDerivative :
    R408.changedStage dataSet ≡ R407.pathDerivativeStage →
    R407.stageOperator (R407.before (R408.ordinaryPair dataSet))
        R407.outerDexpStage
      ≡
    R407.stageOperator (R407.after (R408.ordinaryPair dataSet))
        R407.outerDexpStage →
    R407.stageOperator (R407.before (R408.ordinaryPair dataSet))
        R407.logarithmDexpInverseStage
      ≡
    R407.stageOperator (R407.after (R408.ordinaryPair dataSet))
        R407.logarithmDexpInverseStage →
    R407.stageOperator (R407.before (R408.ordinaryPair dataSet))
        R407.transportDerivativeStage
      ≡
    R407.stageOperator (R407.after (R408.ordinaryPair dataSet))
        R407.transportDerivativeStage →
    SingleChangedFourStageAgreement dataSet

------------------------------------------------------------------------
-- Marked budget family: one resolvent budget, three exact zeros.
------------------------------------------------------------------------

stageMarkedMajorant :
  ∀ {Operator Bound}
    (dataSet : R408.CMP99MarkedR407StageDifference Operator Bound) →
  SingleChangedFourStageAgreement dataSet →
  R407.CMP109DerivativeStage → Bound
stageMarkedMajorant dataSet (changedOuterDexp _ _ _ _)
  R407.outerDexpStage = R408.markedStageMajorant dataSet
stageMarkedMajorant dataSet (changedOuterDexp _ _ _ _)
  R407.logarithmDexpInverseStage = Marked.zeroBound (R408.telescopeAlgebra dataSet)
stageMarkedMajorant dataSet (changedOuterDexp _ _ _ _)
  R407.transportDerivativeStage = Marked.zeroBound (R408.telescopeAlgebra dataSet)
stageMarkedMajorant dataSet (changedOuterDexp _ _ _ _)
  R407.pathDerivativeStage = Marked.zeroBound (R408.telescopeAlgebra dataSet)

stageMarkedMajorant dataSet (changedLogarithmDexpInverse _ _ _ _)
  R407.outerDexpStage = Marked.zeroBound (R408.telescopeAlgebra dataSet)
stageMarkedMajorant dataSet (changedLogarithmDexpInverse _ _ _ _)
  R407.logarithmDexpInverseStage = R408.markedStageMajorant dataSet
stageMarkedMajorant dataSet (changedLogarithmDexpInverse _ _ _ _)
  R407.transportDerivativeStage = Marked.zeroBound (R408.telescopeAlgebra dataSet)
stageMarkedMajorant dataSet (changedLogarithmDexpInverse _ _ _ _)
  R407.pathDerivativeStage = Marked.zeroBound (R408.telescopeAlgebra dataSet)

stageMarkedMajorant dataSet (changedTransportDerivative _ _ _ _)
  R407.outerDexpStage = Marked.zeroBound (R408.telescopeAlgebra dataSet)
stageMarkedMajorant dataSet (changedTransportDerivative _ _ _ _)
  R407.logarithmDexpInverseStage = Marked.zeroBound (R408.telescopeAlgebra dataSet)
stageMarkedMajorant dataSet (changedTransportDerivative _ _ _ _)
  R407.transportDerivativeStage = R408.markedStageMajorant dataSet
stageMarkedMajorant dataSet (changedTransportDerivative _ _ _ _)
  R407.pathDerivativeStage = Marked.zeroBound (R408.telescopeAlgebra dataSet)

stageMarkedMajorant dataSet (changedPathDerivative _ _ _ _)
  R407.outerDexpStage = Marked.zeroBound (R408.telescopeAlgebra dataSet)
stageMarkedMajorant dataSet (changedPathDerivative _ _ _ _)
  R407.logarithmDexpInverseStage = Marked.zeroBound (R408.telescopeAlgebra dataSet)
stageMarkedMajorant dataSet (changedPathDerivative _ _ _ _)
  R407.transportDerivativeStage = Marked.zeroBound (R408.telescopeAlgebra dataSet)
stageMarkedMajorant dataSet (changedPathDerivative _ _ _ _)
  R407.pathDerivativeStage = R408.markedStageMajorant dataSet

changedStageBoundAt :
  ∀ {Operator Bound}
    (dataSet : R408.CMP99MarkedR407StageDifference Operator Bound)
    stage →
  R408.changedStage dataSet ≡ stage →
  Marked.LessEqual (R408.telescopeAlgebra dataSet)
    (Marked.operatorNorm (R408.telescopeAlgebra dataSet)
      (Marked.difference (R408.telescopeAlgebra dataSet)
        (R407.stageOperator (R407.before (R408.ordinaryPair dataSet)) stage)
        (R407.stageOperator (R407.after (R408.ordinaryPair dataSet)) stage)))
    (R408.markedStageMajorant dataSet)
changedStageBoundAt dataSet stage changedIsStage =
  subst
    (λ selectedStage →
      Marked.LessEqual (R408.telescopeAlgebra dataSet)
        (Marked.operatorNorm (R408.telescopeAlgebra dataSet)
          (Marked.difference (R408.telescopeAlgebra dataSet)
            (R407.stageOperator
              (R407.before (R408.ordinaryPair dataSet)) selectedStage)
            (R407.stageOperator
              (R407.after (R408.ordinaryPair dataSet)) selectedStage)))
        (R408.markedStageMajorant dataSet))
    changedIsStage
    (R408.changedStageDifferenceBelowMarkedMajorant dataSet)

stageDifferenceBelowMarkedMajorant :
  ∀ {Operator Bound}
    (dataSet : R408.CMP99MarkedR407StageDifference Operator Bound)
    (agreement : SingleChangedFourStageAgreement dataSet) stage →
  Marked.LessEqual (R408.telescopeAlgebra dataSet)
    (Marked.operatorNorm (R408.telescopeAlgebra dataSet)
      (Marked.difference (R408.telescopeAlgebra dataSet)
        (R407.stageOperator (R407.before (R408.ordinaryPair dataSet)) stage)
        (R407.stageOperator (R407.after (R408.ordinaryPair dataSet)) stage)))
    (stageMarkedMajorant dataSet agreement stage)
stageDifferenceBelowMarkedMajorant dataSet
    (changedOuterDexp changedIs _ _ _) R407.outerDexpStage =
  changedStageBoundAt dataSet R407.outerDexpStage changedIs
stageDifferenceBelowMarkedMajorant dataSet
    (changedOuterDexp _ logEq _ _) R407.logarithmDexpInverseStage =
  R408.unchangedStageDifferenceBelowZero dataSet
    R407.logarithmDexpInverseStage logEq
stageDifferenceBelowMarkedMajorant dataSet
    (changedOuterDexp _ _ transportEq _) R407.transportDerivativeStage =
  R408.unchangedStageDifferenceBelowZero dataSet
    R407.transportDerivativeStage transportEq
stageDifferenceBelowMarkedMajorant dataSet
    (changedOuterDexp _ _ _ pathEq) R407.pathDerivativeStage =
  R408.unchangedStageDifferenceBelowZero dataSet
    R407.pathDerivativeStage pathEq

stageDifferenceBelowMarkedMajorant dataSet
    (changedLogarithmDexpInverse _ outerEq _ _) R407.outerDexpStage =
  R408.unchangedStageDifferenceBelowZero dataSet R407.outerDexpStage outerEq
stageDifferenceBelowMarkedMajorant dataSet
    (changedLogarithmDexpInverse changedIs _ _ _)
    R407.logarithmDexpInverseStage =
  changedStageBoundAt dataSet R407.logarithmDexpInverseStage changedIs
stageDifferenceBelowMarkedMajorant dataSet
    (changedLogarithmDexpInverse _ _ transportEq _)
    R407.transportDerivativeStage =
  R408.unchangedStageDifferenceBelowZero dataSet
    R407.transportDerivativeStage transportEq
stageDifferenceBelowMarkedMajorant dataSet
    (changedLogarithmDexpInverse _ _ _ pathEq) R407.pathDerivativeStage =
  R408.unchangedStageDifferenceBelowZero dataSet R407.pathDerivativeStage pathEq

stageDifferenceBelowMarkedMajorant dataSet
    (changedTransportDerivative _ outerEq _ _) R407.outerDexpStage =
  R408.unchangedStageDifferenceBelowZero dataSet R407.outerDexpStage outerEq
stageDifferenceBelowMarkedMajorant dataSet
    (changedTransportDerivative _ _ logEq _)
    R407.logarithmDexpInverseStage =
  R408.unchangedStageDifferenceBelowZero dataSet
    R407.logarithmDexpInverseStage logEq
stageDifferenceBelowMarkedMajorant dataSet
    (changedTransportDerivative changedIs _ _ _)
    R407.transportDerivativeStage =
  changedStageBoundAt dataSet R407.transportDerivativeStage changedIs
stageDifferenceBelowMarkedMajorant dataSet
    (changedTransportDerivative _ _ _ pathEq) R407.pathDerivativeStage =
  R408.unchangedStageDifferenceBelowZero dataSet R407.pathDerivativeStage pathEq

stageDifferenceBelowMarkedMajorant dataSet
    (changedPathDerivative _ outerEq _ _) R407.outerDexpStage =
  R408.unchangedStageDifferenceBelowZero dataSet R407.outerDexpStage outerEq
stageDifferenceBelowMarkedMajorant dataSet
    (changedPathDerivative _ _ logEq _)
    R407.logarithmDexpInverseStage =
  R408.unchangedStageDifferenceBelowZero dataSet
    R407.logarithmDexpInverseStage logEq
stageDifferenceBelowMarkedMajorant dataSet
    (changedPathDerivative _ _ _ transportEq)
    R407.transportDerivativeStage =
  R408.unchangedStageDifferenceBelowZero dataSet
    R407.transportDerivativeStage transportEq
stageDifferenceBelowMarkedMajorant dataSet
    (changedPathDerivative changedIs _ _ _) R407.pathDerivativeStage =
  changedStageBoundAt dataSet R407.pathDerivativeStage changedIs

------------------------------------------------------------------------
-- Existing Round72 now pays the complete four-stage product replacement.
------------------------------------------------------------------------

fourStageProductDifferenceBelowMarkedMajorant :
  ∀ {Operator Bound}
    (dataSet : R408.CMP99MarkedR407StageDifference Operator Bound)
    (agreement : SingleChangedFourStageAgreement dataSet) →
  Marked.LessEqual (R408.telescopeAlgebra dataSet)
    (Marked.operatorNorm (R408.telescopeAlgebra dataSet)
      (Marked.difference (R408.telescopeAlgebra dataSet)
        (Marked.operatorProduct (R408.telescopeAlgebra dataSet)
          (R407.stageOperator (R407.before (R408.ordinaryPair dataSet)))
          R407.cmp109DerivativeStages)
        (Marked.operatorProduct (R408.telescopeAlgebra dataSet)
          (R407.stageOperator (R407.after (R408.ordinaryPair dataSet)))
          R407.cmp109DerivativeStages)))
    (Marked.markedProductMajorant (R408.telescopeAlgebra dataSet)
      (R407.ordinaryStageMajorant (R408.ordinaryPair dataSet))
      (stageMarkedMajorant dataSet agreement)
      R407.cmp109DerivativeStages)
fourStageProductDifferenceBelowMarkedMajorant dataSet agreement =
  Marked.operatorProductDifferenceFromFactorwiseBounds
    (R408.telescopeAlgebra dataSet)
    (R407.stageOperator (R407.before (R408.ordinaryPair dataSet)))
    (R407.stageOperator (R407.after (R408.ordinaryPair dataSet)))
    (R407.ordinaryStageMajorant (R408.ordinaryPair dataSet))
    (stageMarkedMajorant dataSet agreement)
    R407.cmp109DerivativeStages
    (R408.beforeStageBelowTelescopeOrdinaryMajorant dataSet)
    (R408.afterStageBelowTelescopeOrdinaryMajorant dataSet)
    (stageDifferenceBelowMarkedMajorant dataSet agreement)

------------------------------------------------------------------------
-- Status / Pareto boundary.
------------------------------------------------------------------------

round409FourStageMarkedFamilyCompilerWritten : Bool
round409FourStageMarkedFamilyCompilerWritten = true

round409FourStageMarkedFamilyCompilerWrittenIsTrue :
  round409FourStageMarkedFamilyCompilerWritten ≡ true
round409FourStageMarkedFamilyCompilerWrittenIsTrue = refl

round409WholeProductMarkedInequalityPrimitive : Bool
round409WholeProductMarkedInequalityPrimitive = false

round409WholeProductMarkedInequalityPrimitiveIsFalse :
  round409WholeProductMarkedInequalityPrimitive ≡ false
round409WholeProductMarkedInequalityPrimitiveIsFalse = refl

round409StageChoiceAndEqualitiesStillProofBearing : Bool
round409StageChoiceAndEqualitiesStillProofBearing = true

round409StageChoiceAndEqualitiesStillProofBearingIsTrue :
  round409StageChoiceAndEqualitiesStillProofBearing ≡ true
round409StageChoiceAndEqualitiesStillProofBearingIsTrue = refl

round409SelectedR406ScalarizationWeldStillProofBearing : Bool
round409SelectedR406ScalarizationWeldStillProofBearing = true

round409SelectedR406ScalarizationWeldStillProofBearingIsTrue :
  round409SelectedR406ScalarizationWeldStillProofBearing ≡ true
round409SelectedR406ScalarizationWeldStillProofBearingIsTrue = refl

round409KernelCertifiedAtCurrentHead : Bool
round409KernelCertifiedAtCurrentHead = false

round409KernelCertifiedAtCurrentHeadIsFalse :
  round409KernelCertifiedAtCurrentHead ≡ false
round409KernelCertifiedAtCurrentHeadIsFalse = refl

round409CompilerLevel : ProofLevel
round409CompilerLevel = conditional
