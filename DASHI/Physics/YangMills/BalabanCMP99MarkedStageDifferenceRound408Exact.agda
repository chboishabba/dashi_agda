module DASHI.Physics.YangMills.BalabanCMP99MarkedStageDifferenceRound408Exact where

------------------------------------------------------------------------
-- ROUND408 / CMP99 MARKED CHANGE OF THE ACTUAL R407 STAGE
--
-- R407 pays the ordinary norm bounds for the four CMP109 derivative-entry
-- stages.  R406/Round72 needs, in addition, a marked norm bound for the stage
-- which changes under the CMP99 domain/background replacement.
--
-- The repository already owns the exact analytic compiler for an inverse /
-- propagator change: `BalabanClayGate4ResolventDefectPipelineExact` derives
--
--   ||G_L - G_R|| <= ||G_L|| ||E|| ||G_R||
--
-- from the second resolvent identity and three component norm estimates.
-- Therefore R408 does NOT accept `||A-B|| <= m` as a fresh field.  It asks only
-- for same-object identifications saying that one literal R407 stage difference
-- is that resolvent defect, then transports the already-derived resolvent bound
-- into the noncommutative Round72 algebra used by R406.
--
-- CMP99 Theorem 3.14/(3.154) remains the source authority for the marked
-- domain/background propagator replacement and its distance decay.  The local
-- proof debt after this compiler is the literal same-object attachment of the
-- selected CMP99 defect/budget to the R407 stage, plus the selected R406 term
-- weld and CMP116 positive localization sum.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4OperatorNormPipelineExact as Gate4
import DASHI.Physics.YangMills.BalabanClayGate4ResolventDefectPipelineExact as Resolvent
import DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact as Marked
import DASHI.Physics.YangMills.BalabanCMP109FourStageOperatorFactorRound407Exact as R407

------------------------------------------------------------------------
-- One literal R407 stage identified with one existing resolvent defect.
------------------------------------------------------------------------

record CMP99MarkedR407StageDifference (Operator Bound : Set) : Set₁ where
  field
    ordinaryPair : R407.CMP109FourStageOrdinaryPair Operator Bound

    -- The selected source factor which changes under the domain/background
    -- replacement.  R408 deliberately does not guess which stage by name;
    -- that is a same-object source attachment.
    changedStage : R407.CMP109DerivativeStage

    telescopeAlgebra : Marked.MarkedOperatorNormAlgebra Operator Bound
    resolventData : Resolvent.ResolventIdentityData Operator Bound

    -- R407 ordinary estimates are stated in the Gate4 algebra of the BEFORE
    -- pipeline; R406/Round72 uses the telescope algebra.  These two fields pay
    -- the norm/order representation seam once for every stage.
    gate4NormIsTelescopeNorm : ∀ operator →
      Gate4.operatorNorm (Gate4.algebra (R407.before ordinaryPair)) operator
      ≡ Marked.operatorNorm telescopeAlgebra operator

    gate4OrderToTelescope : ∀ {lower upper} →
      Gate4.LessEqual (Gate4.algebra (R407.before ordinaryPair)) lower upper →
      Marked.LessEqual telescopeAlgebra lower upper

    markedStageMajorant : Bound
    markedStageMajorantIsResolventBudget :
      markedStageMajorant ≡ Resolvent.differenceBudget resolventData

    -- Source/same-object endpoints: the selected R407 before/after stage is the
    -- perturbed/reference inverse carried by the CMP99 resolvent comparison.
    beforeStageIsPerturbedInverse :
      R407.stageOperator (R407.before ordinaryPair) changedStage
      ≡ Resolvent.perturbedInverse resolventData

    afterStageIsReferenceInverse :
      R407.stageOperator (R407.after ordinaryPair) changedStage
      ≡ Resolvent.referenceInverse resolventData

    -- Exact subtraction identification between the R406/Round72 algebra and
    -- the resolvent compiler.  This is representation/same-object glue, not an
    -- extra norm estimate.
    selectedStageDifferenceIsResolventDifference :
      Marked.difference telescopeAlgebra
        (R407.stageOperator (R407.before ordinaryPair) changedStage)
        (R407.stageOperator (R407.after ordinaryPair) changedStage)
      ≡ Resolvent.difference resolventData

    resolventNormIsTelescopeNorm :
      Resolvent.operatorNorm (Resolvent.algebra resolventData)
        (Resolvent.difference resolventData)
      ≡ Marked.operatorNorm telescopeAlgebra
          (Resolvent.difference resolventData)

    resolventOrderToTelescope : ∀ {lower upper} →
      Resolvent.LessEqual (Resolvent.algebra resolventData) lower upper →
      Marked.LessEqual telescopeAlgebra lower upper

open CMP99MarkedR407StageDifference public

------------------------------------------------------------------------
-- R407 ordinary factor bounds transported into the R406/Round72 algebra.
------------------------------------------------------------------------

beforeStageBelowTelescopeOrdinaryMajorant :
  ∀ {Operator Bound}
    (dataSet : CMP99MarkedR407StageDifference Operator Bound) stage →
  Marked.LessEqual (telescopeAlgebra dataSet)
    (Marked.operatorNorm (telescopeAlgebra dataSet)
      (R407.stageOperator
        (R407.before (ordinaryPair dataSet)) stage))
    (R407.ordinaryStageMajorant (ordinaryPair dataSet) stage)
beforeStageBelowTelescopeOrdinaryMajorant dataSet stage =
  subst
    (λ lower →
      Marked.LessEqual (telescopeAlgebra dataSet) lower
        (R407.ordinaryStageMajorant (ordinaryPair dataSet) stage))
    (gate4NormIsTelescopeNorm dataSet
      (R407.stageOperator (R407.before (ordinaryPair dataSet)) stage))
    (gate4OrderToTelescope dataSet
      (R407.beforeStageBelowCommonMajorant (ordinaryPair dataSet) stage))

afterStageBelowTelescopeOrdinaryMajorant :
  ∀ {Operator Bound}
    (dataSet : CMP99MarkedR407StageDifference Operator Bound) stage →
  Marked.LessEqual (telescopeAlgebra dataSet)
    (Marked.operatorNorm (telescopeAlgebra dataSet)
      (R407.stageOperator
        (R407.after (ordinaryPair dataSet)) stage))
    (R407.ordinaryStageMajorant (ordinaryPair dataSet) stage)
afterStageBelowTelescopeOrdinaryMajorant dataSet stage =
  subst
    (λ lower →
      Marked.LessEqual (telescopeAlgebra dataSet) lower
        (R407.ordinaryStageMajorant (ordinaryPair dataSet) stage))
    (gate4NormIsTelescopeNorm dataSet
      (R407.stageOperator (R407.after (ordinaryPair dataSet)) stage))
    (gate4OrderToTelescope dataSet
      (R407.afterStageBelowCommonMajorantOnBeforeAlgebra
        (ordinaryPair dataSet) stage))

------------------------------------------------------------------------
-- The marked changed-stage inequality is compiler output.
------------------------------------------------------------------------

changedStageDifferenceBelowMarkedMajorant :
  ∀ {Operator Bound}
    (dataSet : CMP99MarkedR407StageDifference Operator Bound) →
  Marked.LessEqual (telescopeAlgebra dataSet)
    (Marked.operatorNorm (telescopeAlgebra dataSet)
      (Marked.difference (telescopeAlgebra dataSet)
        (R407.stageOperator
          (R407.before (ordinaryPair dataSet)) (changedStage dataSet))
        (R407.stageOperator
          (R407.after (ordinaryPair dataSet)) (changedStage dataSet))))
    (markedStageMajorant dataSet)
changedStageDifferenceBelowMarkedMajorant dataSet =
  let
    resolventBound :
      Resolvent.LessEqual (Resolvent.algebra (resolventData dataSet))
        (Resolvent.operatorNorm (Resolvent.algebra (resolventData dataSet))
          (Resolvent.difference (resolventData dataSet)))
        (Resolvent.differenceBudget (resolventData dataSet))
    resolventBound =
      Resolvent.resolventDifferenceNormBelowBudget (resolventData dataSet)

    telescopeOrdered :
      Marked.LessEqual (telescopeAlgebra dataSet)
        (Resolvent.operatorNorm (Resolvent.algebra (resolventData dataSet))
          (Resolvent.difference (resolventData dataSet)))
        (Resolvent.differenceBudget (resolventData dataSet))
    telescopeOrdered = resolventOrderToTelescope dataSet resolventBound

    telescopeNormBound :
      Marked.LessEqual (telescopeAlgebra dataSet)
        (Marked.operatorNorm (telescopeAlgebra dataSet)
          (Resolvent.difference (resolventData dataSet)))
        (Resolvent.differenceBudget (resolventData dataSet))
    telescopeNormBound =
      subst
        (λ lower →
          Marked.LessEqual (telescopeAlgebra dataSet) lower
            (Resolvent.differenceBudget (resolventData dataSet)))
        (resolventNormIsTelescopeNorm dataSet)
        telescopeOrdered

    selectedDifferenceBound :
      Marked.LessEqual (telescopeAlgebra dataSet)
        (Marked.operatorNorm (telescopeAlgebra dataSet)
          (Marked.difference (telescopeAlgebra dataSet)
            (R407.stageOperator
              (R407.before (ordinaryPair dataSet)) (changedStage dataSet))
            (R407.stageOperator
              (R407.after (ordinaryPair dataSet)) (changedStage dataSet))))
        (Resolvent.differenceBudget (resolventData dataSet))
    selectedDifferenceBound =
      subst
        (λ selectedDifference →
          Marked.LessEqual (telescopeAlgebra dataSet)
            (Marked.operatorNorm (telescopeAlgebra dataSet) selectedDifference)
            (Resolvent.differenceBudget (resolventData dataSet)))
        (sym (selectedStageDifferenceIsResolventDifference dataSet))
        telescopeNormBound
  in
  subst
    (λ upper →
      Marked.LessEqual (telescopeAlgebra dataSet)
        (Marked.operatorNorm (telescopeAlgebra dataSet)
          (Marked.difference (telescopeAlgebra dataSet)
            (R407.stageOperator
              (R407.before (ordinaryPair dataSet)) (changedStage dataSet))
            (R407.stageOperator
              (R407.after (ordinaryPair dataSet)) (changedStage dataSet))))
        upper)
    (sym (markedStageMajorantIsResolventBudget dataSet))
    selectedDifferenceBound

------------------------------------------------------------------------
-- Literally unchanged stages carry exact zero marked cost.
------------------------------------------------------------------------

unchangedStageDifferenceBelowZero :
  ∀ {Operator Bound}
    (dataSet : CMP99MarkedR407StageDifference Operator Bound)
    stage →
  R407.stageOperator (R407.before (ordinaryPair dataSet)) stage
    ≡ R407.stageOperator (R407.after (ordinaryPair dataSet)) stage →
  Marked.LessEqual (telescopeAlgebra dataSet)
    (Marked.operatorNorm (telescopeAlgebra dataSet)
      (Marked.difference (telescopeAlgebra dataSet)
        (R407.stageOperator (R407.before (ordinaryPair dataSet)) stage)
        (R407.stageOperator (R407.after (ordinaryPair dataSet)) stage)))
    (Marked.zeroBound (telescopeAlgebra dataSet))
unchangedStageDifferenceBelowZero dataSet stage stageEqual =
  subst
    (λ afterStage →
      Marked.LessEqual (telescopeAlgebra dataSet)
        (Marked.operatorNorm (telescopeAlgebra dataSet)
          (Marked.difference (telescopeAlgebra dataSet)
            (R407.stageOperator (R407.before (ordinaryPair dataSet)) stage)
            afterStage))
        (Marked.zeroBound (telescopeAlgebra dataSet)))
    (sym stageEqual)
    (Marked.selfDifferenceNormBound (telescopeAlgebra dataSet)
      (R407.stageOperator (R407.before (ordinaryPair dataSet)) stage))

------------------------------------------------------------------------
-- Status / Pareto boundary.
------------------------------------------------------------------------

round408ChangedStageMarkedInequalityIsCompilerOutput : Bool
round408ChangedStageMarkedInequalityIsCompilerOutput = true

round408ChangedStageMarkedInequalityIsCompilerOutputIsTrue :
  round408ChangedStageMarkedInequalityIsCompilerOutput ≡ true
round408ChangedStageMarkedInequalityIsCompilerOutputIsTrue = refl

round408OrdinaryGate4ToTelescopeTransportWritten : Bool
round408OrdinaryGate4ToTelescopeTransportWritten = true

round408OrdinaryGate4ToTelescopeTransportWrittenIsTrue :
  round408OrdinaryGate4ToTelescopeTransportWritten ≡ true
round408OrdinaryGate4ToTelescopeTransportWrittenIsTrue = refl

round408OpaqueMarkedStageInequalityStillPrimitive : Bool
round408OpaqueMarkedStageInequalityStillPrimitive = false

round408OpaqueMarkedStageInequalityStillPrimitiveIsFalse :
  round408OpaqueMarkedStageInequalityStillPrimitive ≡ false
round408OpaqueMarkedStageInequalityStillPrimitiveIsFalse = refl

round408CMP99ResolventSameObjectAttachmentStillProofBearing : Bool
round408CMP99ResolventSameObjectAttachmentStillProofBearing = true

round408CMP99ResolventSameObjectAttachmentStillProofBearingIsTrue :
  round408CMP99ResolventSameObjectAttachmentStillProofBearing ≡ true
round408CMP99ResolventSameObjectAttachmentStillProofBearingIsTrue = refl

round408UnchangedStagesCanUseExactZeroMarkedBudget : Bool
round408UnchangedStagesCanUseExactZeroMarkedBudget = true

round408UnchangedStagesCanUseExactZeroMarkedBudgetIsTrue :
  round408UnchangedStagesCanUseExactZeroMarkedBudget ≡ true
round408UnchangedStagesCanUseExactZeroMarkedBudgetIsTrue = refl

round408SelectedR406TermWeldStillProofBearing : Bool
round408SelectedR406TermWeldStillProofBearing = true

round408SelectedR406TermWeldStillProofBearingIsTrue :
  round408SelectedR406TermWeldStillProofBearing ≡ true
round408SelectedR406TermWeldStillProofBearingIsTrue = refl

round408KernelCertifiedAtCurrentHead : Bool
round408KernelCertifiedAtCurrentHead = false

round408KernelCertifiedAtCurrentHeadIsFalse :
  round408KernelCertifiedAtCurrentHead ≡ false
round408KernelCertifiedAtCurrentHeadIsFalse = refl

-- Source-written only in this connector tranche; keep non-promotable until an
-- actual Agda/kernel receipt is observed.
round408CompilerLevel : ProofLevel
round408CompilerLevel = conditional
