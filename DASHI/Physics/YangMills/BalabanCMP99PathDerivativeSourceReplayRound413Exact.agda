{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP99PathDerivativeSourceReplayRound413Exact where

------------------------------------------------------------------------
-- ROUND413 / SOURCE-SHAPED CMP99 THEOREM 3.14 -> R410 PATH STAGE
--
-- R408 deliberately allows an arbitrary changed R407 stage.  The actual source
-- reading is stronger and simpler: CMP109's substituted-background dependence
-- enters through the innermost path/background derivative, and CMP99 3.14 /
-- (3.154) replaces precisely that propagator/background factor.
--
-- This owner therefore fixes the changed stage definitionally to the path
-- derivative stage and compiles the source-shaped replacement directly into
-- R408 and R410.  The caller no longer supplies a stage choice or a proof that
-- the chosen stage is the path stage.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4OperatorNormPipelineExact as Gate4
import DASHI.Physics.YangMills.BalabanClayGate4ResolventDefectPipelineExact as Resolvent
import DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact as Marked
import DASHI.Physics.YangMills.BalabanCMP109FourStageOperatorFactorRound407Exact as R407
import DASHI.Physics.YangMills.BalabanCMP99MarkedStageDifferenceRound408Exact as R408
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410

record CMP99PathDerivativeSourceReplay
    (Operator Bound : Set) : Set₁ where
  field
    ordinaryPair : R407.CMP109FourStageOrdinaryPair Operator Bound
    telescopeAlgebra : Marked.MarkedOperatorNormAlgebra Operator Bound
    resolventData : Resolvent.ResolventIdentityData Operator Bound

    gate4NormIsTelescopeNorm : ∀ operator →
      Gate4.operatorNorm (Gate4.algebra (R407.before ordinaryPair)) operator
      ≡ Marked.operatorNorm telescopeAlgebra operator

    gate4OrderToTelescope : ∀ {lower upper} →
      Gate4.LessEqual (Gate4.algebra (R407.before ordinaryPair)) lower upper →
      Marked.LessEqual telescopeAlgebra lower upper

    beforePathDerivativeIsPerturbedInverse :
      R407.stageOperator (R407.before ordinaryPair) R407.pathDerivativeStage
      ≡ Resolvent.perturbedInverse resolventData

    afterPathDerivativeIsReferenceInverse :
      R407.stageOperator (R407.after ordinaryPair) R407.pathDerivativeStage
      ≡ Resolvent.referenceInverse resolventData

    pathDerivativeDifferenceIsResolventDifference :
      Marked.difference telescopeAlgebra
        (R407.stageOperator (R407.before ordinaryPair) R407.pathDerivativeStage)
        (R407.stageOperator (R407.after ordinaryPair) R407.pathDerivativeStage)
      ≡ Resolvent.difference resolventData

    resolventNormIsTelescopeNorm :
      Resolvent.operatorNorm (Resolvent.algebra resolventData)
        (Resolvent.difference resolventData)
      ≡ Marked.operatorNorm telescopeAlgebra
          (Resolvent.difference resolventData)

    resolventOrderToTelescope : ∀ {lower upper} →
      Resolvent.LessEqual (Resolvent.algebra resolventData) lower upper →
      Marked.LessEqual telescopeAlgebra lower upper

    outerDexpUnchanged :
      R407.stageOperator (R407.before ordinaryPair) R407.outerDexpStage
      ≡ R407.stageOperator (R407.after ordinaryPair) R407.outerDexpStage

    logarithmDexpInverseUnchanged :
      R407.stageOperator
        (R407.before ordinaryPair) R407.logarithmDexpInverseStage
      ≡ R407.stageOperator
        (R407.after ordinaryPair) R407.logarithmDexpInverseStage

    transportDerivativeUnchanged :
      R407.stageOperator
        (R407.before ordinaryPair) R407.transportDerivativeStage
      ≡ R407.stageOperator
        (R407.after ordinaryPair) R407.transportDerivativeStage

open CMP99PathDerivativeSourceReplay public

asR408StageDifference :
  ∀ {Operator Bound} →
  CMP99PathDerivativeSourceReplay Operator Bound →
  R408.CMP99MarkedR407StageDifference Operator Bound
asR408StageDifference source = record
  { R408.CMP99MarkedR407StageDifference.ordinaryPair =
      ordinaryPair source
  ; R408.CMP99MarkedR407StageDifference.changedStage =
      R407.pathDerivativeStage
  ; R408.CMP99MarkedR407StageDifference.telescopeAlgebra =
      telescopeAlgebra source
  ; R408.CMP99MarkedR407StageDifference.resolventData =
      resolventData source
  ; R408.CMP99MarkedR407StageDifference.gate4NormIsTelescopeNorm =
      gate4NormIsTelescopeNorm source
  ; R408.CMP99MarkedR407StageDifference.gate4OrderToTelescope =
      gate4OrderToTelescope source
  ; R408.CMP99MarkedR407StageDifference.markedStageMajorant =
      Resolvent.differenceBudget (resolventData source)
  ; R408.CMP99MarkedR407StageDifference.markedStageMajorantIsResolventBudget =
      refl
  ; R408.CMP99MarkedR407StageDifference.beforeStageIsPerturbedInverse =
      beforePathDerivativeIsPerturbedInverse source
  ; R408.CMP99MarkedR407StageDifference.afterStageIsReferenceInverse =
      afterPathDerivativeIsReferenceInverse source
  ; R408.CMP99MarkedR407StageDifference.selectedStageDifferenceIsResolventDifference =
      pathDerivativeDifferenceIsResolventDifference source
  ; R408.CMP99MarkedR407StageDifference.resolventNormIsTelescopeNorm =
      resolventNormIsTelescopeNorm source
  ; R408.CMP99MarkedR407StageDifference.resolventOrderToTelescope =
      resolventOrderToTelescope source
  }

asR410CanonicalPathReplay :
  ∀ {Operator Bound} →
  CMP99PathDerivativeSourceReplay Operator Bound →
  R410.CanonicalPathMarkedCMP109Replay Operator Bound
asR410CanonicalPathReplay source = record
  { R410.CanonicalPathMarkedCMP109Replay.stageDifference =
      asR408StageDifference source
  ; R410.CanonicalPathMarkedCMP109Replay.changedStageIsPathDerivative =
      refl
  ; R410.CanonicalPathMarkedCMP109Replay.outerDexpUnchanged =
      outerDexpUnchanged source
  ; R410.CanonicalPathMarkedCMP109Replay.logarithmDexpInverseUnchanged =
      logarithmDexpInverseUnchanged source
  ; R410.CanonicalPathMarkedCMP109Replay.transportDerivativeUnchanged =
      transportDerivativeUnchanged source
  }

cmp99PathDefectBelowResolventBudget :
  ∀ {Operator Bound}
    (source : CMP99PathDerivativeSourceReplay Operator Bound) →
  Marked.LessEqual (telescopeAlgebra source)
    (Marked.operatorNorm (telescopeAlgebra source)
      (Marked.difference (telescopeAlgebra source)
        (R407.stageOperator
          (R407.before (ordinaryPair source)) R407.pathDerivativeStage)
        (R407.stageOperator
          (R407.after (ordinaryPair source)) R407.pathDerivativeStage)))
    (Resolvent.differenceBudget (resolventData source))
cmp99PathDefectBelowResolventBudget source =
  R408.changedStageDifferenceBelowMarkedMajorant
    (asR408StageDifference source)

round413CMP99PathStageChoiceCompilerLevel : ProofLevel
round413CMP99PathStageChoiceCompilerLevel = machineChecked

round413CMP99ToR410ReplayCompilerLevel : ProofLevel
round413CMP99ToR410ReplayCompilerLevel = machineChecked

literalCMP99Theorem314PathDerivativeAttachmentLevel : ProofLevel
literalCMP99Theorem314PathDerivativeAttachmentLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
