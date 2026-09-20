{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact where

------------------------------------------------------------------------
-- ROUND410 / CANONICAL CMP99-MARKED PATH/BACKGROUND DERIVATIVE REPLAY
--
-- CMP109 (4.3) differentiates the substituted background H_j(Π_0,0).
-- CMP99 Theorem 3.14/(3.154) is precisely the marked replacement theorem for
-- that background-propagator/random-walk derivative.  On the four-stage chain
--
--   path/background derivative
--     -> transport
--     -> dexp^{-1}/log
--     -> outer dexp
--
-- the source replacement is therefore carried by the innermost path derivative.
-- The three surrounding chain-rule maps are unchanged.
--
-- This owner removes R409's four-way changed-stage ambiguity on the preferred
-- source route and proves the exact four-stage marked product bound.  The only
-- source/application payments retained are the literal same-object identities:
--   * R408's resolvent defect really is the selected path/background derivative;
--   * outer/transport/logarithm stages are unchanged;
--   * the selected CMP116 differentiated scalar term is the norm of this exact
--     four-stage product difference.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ; _≤ℝ_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact as Marked
import DASHI.Physics.YangMills.BalabanCMP109FourStageOperatorFactorRound407Exact as R407
import DASHI.Physics.YangMills.BalabanCMP99MarkedStageDifferenceRound408Exact as R408
import DASHI.Physics.YangMills.BalabanCMP99SingleMarkedFourStageRound409Exact as R409

record CanonicalPathMarkedCMP109Replay
    (Operator Bound : Set) : Set₁ where
  field
    stageDifference : R408.CMP99MarkedR407StageDifference Operator Bound

    changedStageIsPathDerivative :
      R408.changedStage stageDifference ≡ R407.pathDerivativeStage

    outerDexpUnchanged :
      R407.stageOperator
        (R407.before (R408.ordinaryPair stageDifference))
        R407.outerDexpStage
      ≡
      R407.stageOperator
        (R407.after (R408.ordinaryPair stageDifference))
        R407.outerDexpStage

    logarithmDexpInverseUnchanged :
      R407.stageOperator
        (R407.before (R408.ordinaryPair stageDifference))
        R407.logarithmDexpInverseStage
      ≡
      R407.stageOperator
        (R407.after (R408.ordinaryPair stageDifference))
        R407.logarithmDexpInverseStage

    transportDerivativeUnchanged :
      R407.stageOperator
        (R407.before (R408.ordinaryPair stageDifference))
        R407.transportDerivativeStage
      ≡
      R407.stageOperator
        (R407.after (R408.ordinaryPair stageDifference))
        R407.transportDerivativeStage

open CanonicalPathMarkedCMP109Replay public

canonicalSingleChangedAgreement :
  ∀ {Operator Bound}
    (replay : CanonicalPathMarkedCMP109Replay Operator Bound) →
  R409.SingleChangedFourStageAgreement (stageDifference replay)
canonicalSingleChangedAgreement replay =
  R409.changedPathDerivative
    (changedStageIsPathDerivative replay)
    (outerDexpUnchanged replay)
    (logarithmDexpInverseUnchanged replay)
    (transportDerivativeUnchanged replay)

canonicalFourStageProductDifferenceBelowMarkedMajorant :
  ∀ {Operator Bound}
    (replay : CanonicalPathMarkedCMP109Replay Operator Bound) →
  Marked.LessEqual (R408.telescopeAlgebra (stageDifference replay))
    (Marked.operatorNorm (R408.telescopeAlgebra (stageDifference replay))
      (Marked.difference (R408.telescopeAlgebra (stageDifference replay))
        (Marked.operatorProduct
          (R408.telescopeAlgebra (stageDifference replay))
          (R407.stageOperator
            (R407.before (R408.ordinaryPair (stageDifference replay))))
          R407.cmp109DerivativeStages)
        (Marked.operatorProduct
          (R408.telescopeAlgebra (stageDifference replay))
          (R407.stageOperator
            (R407.after (R408.ordinaryPair (stageDifference replay))))
          R407.cmp109DerivativeStages)))
    (Marked.markedProductMajorant
      (R408.telescopeAlgebra (stageDifference replay))
      (R407.ordinaryStageMajorant
        (R408.ordinaryPair (stageDifference replay)))
      (R409.stageMarkedMajorant
        (stageDifference replay)
        (canonicalSingleChangedAgreement replay))
      R407.cmp109DerivativeStages)
canonicalFourStageProductDifferenceBelowMarkedMajorant replay =
  R409.fourStageProductDifferenceBelowMarkedMajorant
    (stageDifference replay)
    (canonicalSingleChangedAgreement replay)

------------------------------------------------------------------------
-- Exact scalarization of the selected differentiated CMP116 term.
------------------------------------------------------------------------

record SelectedCMP116PathMarkedTerm
    (Operator : Set) : Set₁ where
  field
    replay : CanonicalPathMarkedCMP109Replay Operator
      ℝ

    differentiatedTerm : ℝ

    differentiatedTermAbsoluteIsCanonicalProductDifferenceNorm :
      absℝ differentiatedTerm
      ≡
      Marked.operatorNorm (R408.telescopeAlgebra (stageDifference replay))
        (Marked.difference (R408.telescopeAlgebra (stageDifference replay))
          (Marked.operatorProduct
            (R408.telescopeAlgebra (stageDifference replay))
            (R407.stageOperator
              (R407.before (R408.ordinaryPair (stageDifference replay))))
            R407.cmp109DerivativeStages)
          (Marked.operatorProduct
            (R408.telescopeAlgebra (stageDifference replay))
            (R407.stageOperator
              (R407.after (R408.ordinaryPair (stageDifference replay))))
            R407.cmp109DerivativeStages))

open SelectedCMP116PathMarkedTerm public

selectedDifferentiatedTermBelowCanonicalMarkedProduct :
  ∀ {Operator}
    (term : SelectedCMP116PathMarkedTerm Operator) →
  _≤ℝ_
    (absℝ
      (differentiatedTerm term))
    (Marked.markedProductMajorant
      (R408.telescopeAlgebra (stageDifference (replay term)))
      (R407.ordinaryStageMajorant
        (R408.ordinaryPair (stageDifference (replay term))))
      (R409.stageMarkedMajorant
        (stageDifference (replay term))
        (canonicalSingleChangedAgreement (replay term)))
      R407.cmp109DerivativeStages)
selectedDifferentiatedTermBelowCanonicalMarkedProduct term =
  subst
    (λ lower →
      _≤ℝ_ lower
        (Marked.markedProductMajorant
          (R408.telescopeAlgebra (stageDifference (replay term)))
          (R407.ordinaryStageMajorant
            (R408.ordinaryPair (stageDifference (replay term))))
          (R409.stageMarkedMajorant
            (stageDifference (replay term))
            (canonicalSingleChangedAgreement (replay term)))
          R407.cmp109DerivativeStages))
    (differentiatedTermAbsoluteIsCanonicalProductDifferenceNorm term)
    (canonicalFourStageProductDifferenceBelowMarkedMajorant (replay term))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round410ChangedStageChoiceCompilerLevel : ProofLevel
round410ChangedStageChoiceCompilerLevel = machineChecked

round410FourStageProductCompilerLevel : ProofLevel
round410FourStageProductCompilerLevel = machineChecked

round410SelectedTermBoundCompilerLevel : ProofLevel
round410SelectedTermBoundCompilerLevel = machineChecked

-- Literal source/application equalities still to instantiate on the selected
-- CMP99/CMP109/CMP116 object.  The four-way stage-choice ambiguity is gone.
literalCMP99PathDerivativeResolventAttachmentLevel : ProofLevel
literalCMP99PathDerivativeResolventAttachmentLevel = conditional

literalCMP109OuterThreeStagesUnchangedLevel : ProofLevel
literalCMP109OuterThreeStagesUnchangedLevel = conditional

literalCMP116SelectedTermScalarizationLevel : ProofLevel
literalCMP116SelectedTermScalarizationLevel = conditional
