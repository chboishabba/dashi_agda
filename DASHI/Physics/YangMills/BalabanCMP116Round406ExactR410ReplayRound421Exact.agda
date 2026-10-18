{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116Round406ExactR410ReplayRound421Exact where

------------------------------------------------------------------------
-- B / ROUND421: R406 OPERATOR FACTOR REPLAY -> EXACT R410 TERM
--
-- R406 already stores the literal differentiated scalar together with the
-- norm of its noncommutative before/after product.  R410 stores the same
-- scalar behind a fixed four-stage path/background replay.
--
-- Therefore the scalar equality requested by Round406ExactR410Replay is not
-- an independent source fact: choose the R410 term's scalar definitionally to
-- be the R406 scalar.  The only genuine same-object payments are:
--
--   * the R406 product-difference norm is the R410 four-stage product norm;
--   * the R406 marked-product majorant is the canonical R410 majorant.
--
-- This compiler constructs the R410 term and proves the scalar equality by
-- refl.  It narrows B1 from "term + majorant equality" to the actual
-- operator/factor-layout attachment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact as Marked
import DASHI.Physics.YangMills.BalabanCMP109FourStageOperatorFactorRound407Exact as R407
import DASHI.Physics.YangMills.BalabanCMP99MarkedStageDifferenceRound408Exact as R408
import DASHI.Physics.YangMills.BalabanCMP99SingleMarkedFourStageRound409Exact as R409
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact as R415
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP116Round406To415Exact as R406R415

record LiteralRound406R410OperatorReplay
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    : Set₁ where
  field
    canonicalPathReplay :
      ∀ domain term →
      R410.CanonicalPathMarkedCMP109Replay
        (R406.Operator application)
        ℝ

    -- Same-object scalarization seam.  R406 already proves that the absolute
    -- scalar is its product-difference norm; this field identifies that norm
    -- with the fixed four-stage R410 product norm.
    r406ProductNormIsCanonicalR410ProductNorm :
      ∀ domain term →
      Marked.operatorNorm (R406.operatorAlgebra application)
        (Marked.difference (R406.operatorAlgebra application)
          (Marked.operatorProduct
            (R406.operatorAlgebra application)
            (R406.beforeOperator application domain term)
            (R406.termFactors application domain term))
          (Marked.operatorProduct
            (R406.operatorAlgebra application)
            (R406.afterOperator application domain term)
            (R406.termFactors application domain term)))
      ≡
      Marked.operatorNorm
        (R408.telescopeAlgebra
          (R410.stageDifference (canonicalPathReplay domain term)))
        (Marked.difference
          (R408.telescopeAlgebra
            (R410.stageDifference (canonicalPathReplay domain term)))
          (Marked.operatorProduct
            (R408.telescopeAlgebra
              (R410.stageDifference (canonicalPathReplay domain term)))
            (R407.stageOperator
              (R407.before
                (R408.ordinaryPair
                  (R410.stageDifference
                    (canonicalPathReplay domain term)))))
            R407.cmp109DerivativeStages)
          (Marked.operatorProduct
            (R408.telescopeAlgebra
              (R410.stageDifference (canonicalPathReplay domain term)))
            (R407.stageOperator
              (R407.after
                (R408.ordinaryPair
                  (R410.stageDifference
                    (canonicalPathReplay domain term)))))
            R407.cmp109DerivativeStages))

    -- Same-object majorant seam.  This is exactly the canonical R410 product
    -- majorant, written without first postulating an R410 selected term.
    r406MajorantIsCanonicalR410Majorant :
      ∀ domain term →
      R406.differentiatedTermMajorant application domain term
      ≡
      Marked.markedProductMajorant
        (R408.telescopeAlgebra
          (R410.stageDifference (canonicalPathReplay domain term)))
        (R407.ordinaryStageMajorant
          (R408.ordinaryPair
            (R410.stageDifference (canonicalPathReplay domain term))))
        (R409.stageMarkedMajorant
          (R410.stageDifference (canonicalPathReplay domain term))
          (R410.canonicalSingleChangedAgreement
            (canonicalPathReplay domain term)))
        R407.cmp109DerivativeStages

open LiteralRound406R410OperatorReplay public

selectedR410TermFromOperatorReplay :
  ∀ {Measure TestObservable dataSet extension base application}
    (replayData :
      LiteralRound406R410OperatorReplay
        {Measure = Measure}
        {TestObservable = TestObservable}
        {dataSet = dataSet}
        {extension = extension}
        {base = base}
        application) →
  ∀ domain term →
  R410.SelectedCMP116PathMarkedTerm (R406.Operator application)
selectedR410TermFromOperatorReplay {application = application}
    replayData domain term = record
  { R410.SelectedCMP116PathMarkedTerm.replay =
      canonicalPathReplay replayData domain term
  ; R410.SelectedCMP116PathMarkedTerm.differentiatedTerm =
      R406.differentiatedTerm application domain term
  ; R410.SelectedCMP116PathMarkedTerm.differentiatedTermAbsoluteIsCanonicalProductDifferenceNorm =
      trans
        (R406.differentiatedTermAbsoluteIsOperatorDifferenceNorm
          application domain term)
        (r406ProductNormIsCanonicalR410ProductNorm replayData domain term)
  }

r406ScalarTermIsCompiledR410Term :
  ∀ {Measure TestObservable dataSet extension base application}
    (replayData :
      LiteralRound406R410OperatorReplay
        {Measure = Measure}
        {TestObservable = TestObservable}
        {dataSet = dataSet}
        {extension = extension}
        {base = base}
        application) →
  ∀ domain term →
  R406.differentiatedTerm application domain term
  ≡
  R410.differentiatedTerm
    (selectedR410TermFromOperatorReplay replayData domain term)
r406ScalarTermIsCompiledR410Term replayData domain term = refl

r406MajorantIsCompiledR410Majorant :
  ∀ {Measure TestObservable dataSet extension base application}
    (replayData :
      LiteralRound406R410OperatorReplay
        {Measure = Measure}
        {TestObservable = TestObservable}
        {dataSet = dataSet}
        {extension = extension}
        {base = base}
        application) →
  ∀ domain term →
  R406.differentiatedTermMajorant application domain term
  ≡
  R415.canonicalTermMajorant
    (selectedR410TermFromOperatorReplay replayData domain term)
r406MajorantIsCompiledR410Majorant replayData domain term =
  r406MajorantIsCanonicalR410Majorant replayData domain term

compileExactR410Replay :
  ∀ {Measure TestObservable dataSet extension base}
    (application : R406.SelectedCMP116TermwiseLocalization base) →
  LiteralRound406R410OperatorReplay
    {Measure = Measure}
    {TestObservable = TestObservable}
    {dataSet = dataSet}
    {extension = extension}
    {base = base}
    application →
  R406R415.Round406ExactR410Replay application
compileExactR410Replay application replayData = record
  { R406R415.Round406ExactR410Replay.selectedR410Term =
      selectedR410TermFromOperatorReplay replayData
  ; R406R415.Round406ExactR410Replay.differentiatedTermIsR410 =
      r406ScalarTermIsCompiledR410Term replayData
  ; R406R415.Round406ExactR410Replay.differentiatedMajorantIsCanonicalR410 =
      r406MajorantIsCompiledR410Majorant replayData
  }

round421ScalarTermEqualityCompilerLevel : ProofLevel
round421ScalarTermEqualityCompilerLevel = machineChecked

round421ExactR410ReplayCompilerLevel : ProofLevel
round421ExactR410ReplayCompilerLevel = machineChecked

round421SeparateScalarTermEqualityLeafRequired : Bool
round421SeparateScalarTermEqualityLeafRequired = false

round421SeparateScalarTermEqualityLeafRequiredIsFalse :
  round421SeparateScalarTermEqualityLeafRequired ≡ false
round421SeparateScalarTermEqualityLeafRequiredIsFalse = refl

-- Remaining B1 payment: attach the R406 abstract factor product to the fixed
-- CMP99/CMP109 four-stage path replay, including its canonical majorant.
literalRound406R410OperatorFactorLayoutAttachmentLevel : ProofLevel
literalRound406R410OperatorFactorLayoutAttachmentLevel = conditional
