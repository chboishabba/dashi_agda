{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R413ToR406RefinementRound422Exact where

------------------------------------------------------------------------
-- ROUND422 / LITERAL CMP99 PATH REPLAY -> R406/R410 TERMWISE REFINEMENT
--
-- R417 showed that the detailed R415 lane does not need to reconstruct R406's
-- literal source expansion.  It only needs each existing R406 term refined to
-- the canonical R410 marked-path term.
--
-- R413 already constructs the canonical R410 replay from the source-shaped
-- CMP99 theorem-3.14 path/background replacement.  Therefore callers should
-- not separately build an R410 replay.  This owner asks only for:
--
--   * the literal R413 source replay for each existing R406 term;
--   * the selected R406 scalar is the norm of THAT canonical product difference;
--   * the selected R406 majorant is THAT canonical R410 marked majorant.
--
-- Stage choice, unchanged-stage equalities -> zero marked cost, ordinary stage
-- bounds, resolvent inequality, and the four-stage product telescope remain
-- compiler-owned.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP109FourStageOperatorFactorRound407Exact as R407
import DASHI.Physics.YangMills.BalabanCMP99MarkedStageDifferenceRound408Exact as R408
import DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact as Marked
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410
import DASHI.Physics.YangMills.BalabanCMP99PathDerivativeSourceReplayRound413Exact as R413
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact as R415
import DASHI.Physics.YangMills.BalabanCMP116R406ToSelectedMarkedExpansionRound417Exact as R417

record R413TermwiseR406Attachment
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base) : Set₂ where
  field
    sourceReplay :
      R406.Domain application →
      R406.Term application →
      R413.CMP99PathDerivativeSourceReplay (R406.Operator application) ℝ

    selectedScalarization :
      ∀ domain term →
      absℝ (R406.differentiatedTerm application domain term)
      ≡
      let replay = R413.asR410CanonicalPathReplay (sourceReplay domain term)
      in
      Marked.operatorNorm
        (R408.telescopeAlgebra (R410.stageDifference replay))
        (Marked.difference
          (R408.telescopeAlgebra (R410.stageDifference replay))
          (Marked.operatorProduct
            (R408.telescopeAlgebra (R410.stageDifference replay))
            (R407.stageOperator
              (R407.before (R408.ordinaryPair (R410.stageDifference replay))))
            R407.cmp109DerivativeStages)
          (Marked.operatorProduct
            (R408.telescopeAlgebra (R410.stageDifference replay))
            (R407.stageOperator
              (R407.after (R408.ordinaryPair (R410.stageDifference replay))))
            R407.cmp109DerivativeStages))

    selectedMajorantIsCanonical :
      ∀ domain term →
      let selected = selectedR410Term domain term
      in
      R406.differentiatedTermMajorant application domain term
      ≡ R415.canonicalTermMajorant selected

  selectedR410Term :
    R406.Domain application →
    R406.Term application →
    R410.SelectedCMP116PathMarkedTerm (R406.Operator application)
  selectedR410Term domain term = record
    { R410.SelectedCMP116PathMarkedTerm.replay =
        R413.asR410CanonicalPathReplay (sourceReplay domain term)
    ; R410.SelectedCMP116PathMarkedTerm.differentiatedTerm =
        R406.differentiatedTerm application domain term
    ; R410.SelectedCMP116PathMarkedTerm.differentiatedTermAbsoluteIsCanonicalProductDifferenceNorm =
        selectedScalarization domain term
    }

open R413TermwiseR406Attachment public

asR417Refinement :
  ∀ {Measure TestObservable dataSet extension base application} →
  R413TermwiseR406Attachment
    {dataSet = dataSet} {extension = extension} {base = base}
    application →
  R417.R406CanonicalR410Refinement application
asR417Refinement attachment = record
  { R417.R406CanonicalR410Refinement.selectedTerm =
      selectedR410Term attachment
  ; R417.R406CanonicalR410Refinement.selectedTermScalarIsR406Scalar =
      λ domain term → refl
  ; R417.R406CanonicalR410Refinement.r406MajorantIsCanonicalR410Majorant =
      selectedMajorantIsCanonical attachment
  }

round422R413ToR406RefinementCompilerLevel : ProofLevel
round422R413ToR406RefinementCompilerLevel = machineChecked

-- Stage choice and the complete R410 replay are no longer independent inputs.
round422IndependentR410ReplayRequired : Bool
round422IndependentR410ReplayRequired = false

-- Genuine source seam: literal CMP99 path replacement + selected scalar/majorant
-- same-object attachment on each existing R406 source term.
round422LiteralCMP99PathAttachmentLevel : ProofLevel
round422LiteralCMP99PathAttachmentLevel = conditional

round422SelectedTermScalarizationLevel : ProofLevel
round422SelectedTermScalarizationLevel = conditional

round422SelectedMajorantSameObjectLevel : ProofLevel
round422SelectedMajorantSameObjectLevel = conditional
