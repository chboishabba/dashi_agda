{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R409SelectedTermReplayRound410Exact where

------------------------------------------------------------------------
-- ROUND410 / R409 SOURCE TERM REPLAY -> COMPLETE R406 FACTOR PAYMENT
--
-- R407 owns the literal four CMP109 derivative stages and ordinary bounds.
-- R408 derives the one genuinely changed CMP99/resolvent stage estimate.
-- R409 makes the remaining three stages exact-zero marked costs.
--
-- Therefore a selected CMP116 term should not carry any factorwise inequalities
-- by hand.  Once a source replay chooses an R408/R409 object for that term and
-- identifies the scalar differentiated term with the norm of the corresponding
-- four-stage product difference, all R406 operator-factor obligations are
-- compiler output.
--
-- What remains source-facing here is only:
--   * the selected density/J/decoupling identity;
--   * the scalarization of the literal (1.23) term as the selected four-stage
--     CMP109 product difference;
--   * the positive common-Y and outer CMP116 sums.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact as Marked
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP109FourStageOperatorFactorRound407Exact as R407
import DASHI.Physics.YangMills.BalabanCMP99MarkedStageDifferenceRound408Exact as R408
import DASHI.Physics.YangMills.BalabanCMP99SingleMarkedFourStageRound409Exact as R409

record SelectedCMP116R409TermReplay
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    : Set₁ where
  field
    selectedT5RGDensity : Set
    selectedT5RGDensityIsBase :
      selectedT5RGDensity ≡ R318.SourceDirection base

    leftObservable rightObservable : R318.SourceDirection base
    leftJ rightJ : R318.SourceDirection base
    leftJIsObservableIndexed :
      leftJ ≡ Cumulant.sourceDirectionOf (R318.meaning base) leftObservable
    rightJIsObservableIndexed :
      rightJ ≡ Cumulant.sourceDirectionOf (R318.meaning base) rightObservable

    DecouplingBoundaryAssignment : Set
    selectedDecouplingBoundary : DecouplingBoundaryAssignment

    Term Domain Operator : Set
    localizedDomains : List Domain
    termsWithCommonY : Domain → List Term
    differentiatedTerm : Domain → Term → ℝ
    commonYBoundaryIntegrand commonYShell : Domain → ℝ
    selectedBoundaryIntegrand selectedConnectingShell : ℝ

    -- One common selected operator-norm algebra.  Every source term replay is
    -- required to inhabit this SAME algebra; this prevents silently mixing
    -- norm conventions across the localization sum.
    operatorAlgebra : Marked.MarkedOperatorNormAlgebra Operator ℝ

    termReplay :
      (domain : Domain) → (term : Term) →
      R408.CMP99MarkedR407StageDifference Operator ℝ

    singleChangedAgreement :
      ∀ domain term →
      R409.SingleChangedFourStageAgreement (termReplay domain term)

    termReplayUsesSelectedAlgebra :
      ∀ domain term →
      R408.telescopeAlgebra (termReplay domain term) ≡ operatorAlgebra

    -- Exact source/same-object scalarization.  This is not an inequality:
    -- it says which literal CMP116 differentiated contribution the selected
    -- four-stage CMP109 source expression denotes.
    differentiatedTermAbsoluteIsFourStageDifferenceNorm :
      ∀ domain term →
      absℝ (differentiatedTerm domain term)
      ≡
      Marked.operatorNorm operatorAlgebra
        (Marked.difference operatorAlgebra
          (Marked.operatorProduct operatorAlgebra
            (R407.stageOperator
              (R407.before
                (R408.ordinaryPair (termReplay domain term))))
            R407.cmp109DerivativeStages)
          (Marked.operatorProduct operatorAlgebra
            (R407.stageOperator
              (R407.after
                (R408.ordinaryPair (termReplay domain term))))
            R407.cmp109DerivativeStages))

    selectedBoundaryIsCommonYSum :
      selectedBoundaryIntegrand
      ≡ Resum.sumℝ commonYBoundaryIntegrand localizedDomains

    commonYBoundaryIsTermSum :
      ∀ domain →
      commonYBoundaryIntegrand domain
      ≡ Resum.sumℝ
          (differentiatedTerm domain)
          (termsWithCommonY domain)

    differentiatedMajorantsBelowCommonYShell :
      ∀ domain →
      Resum.sumℝ
        (λ term →
          Marked.markedProductMajorant operatorAlgebra
            (R407.ordinaryStageMajorant
              (R408.ordinaryPair (termReplay domain term)))
            (R409.stageMarkedMajorant
              (termReplay domain term)
              (singleChangedAgreement domain term))
            R407.cmp109DerivativeStages)
        (termsWithCommonY domain)
      ≤ℝ commonYShell domain

    commonYShellsBelowSelectedConnectingShell :
      Resum.sumℝ commonYShell localizedDomains
      ≤ℝ selectedConnectingShell

open SelectedCMP116R409TermReplay public

termMajorant :
  ∀ {Measure TestObservable dataSet extension base}
    (replay : SelectedCMP116R409TermReplay
      {Measure = Measure} {TestObservable = TestObservable}
      {dataSet = dataSet} {extension = extension} base) →
  Domain replay → Term replay → ℝ
termMajorant replay domain term =
  Marked.markedProductMajorant (operatorAlgebra replay)
    (R407.ordinaryStageMajorant
      (R408.ordinaryPair (termReplay replay domain term)))
    (R409.stageMarkedMajorant
      (termReplay replay domain term)
      (singleChangedAgreement replay domain term))
    R407.cmp109DerivativeStages

beforeStage :
  ∀ {Measure TestObservable dataSet extension base}
    (replay : SelectedCMP116R409TermReplay
      {Measure = Measure} {TestObservable = TestObservable}
      {dataSet = dataSet} {extension = extension} base) →
  Domain replay → Term replay → R407.CMP109DerivativeStage → Operator replay
beforeStage replay domain term =
  R407.stageOperator
    (R407.before (R408.ordinaryPair (termReplay replay domain term)))

afterStage :
  ∀ {Measure TestObservable dataSet extension base}
    (replay : SelectedCMP116R409TermReplay
      {Measure = Measure} {TestObservable = TestObservable}
      {dataSet = dataSet} {extension = extension} base) →
  Domain replay → Term replay → R407.CMP109DerivativeStage → Operator replay
afterStage replay domain term =
  R407.stageOperator
    (R407.after (R408.ordinaryPair (termReplay replay domain term)))

beforeStageBelowSelectedOrdinary :
  ∀ {Measure TestObservable dataSet extension base}
    (replay : SelectedCMP116R409TermReplay
      {Measure = Measure} {TestObservable = TestObservable}
      {dataSet = dataSet} {extension = extension} base) →
  ∀ domain term stage →
  Marked.LessEqual (operatorAlgebra replay)
    (Marked.operatorNorm (operatorAlgebra replay)
      (beforeStage replay domain term stage))
    (R407.ordinaryStageMajorant
      (R408.ordinaryPair (termReplay replay domain term)) stage)
beforeStageBelowSelectedOrdinary replay domain term stage =
  subst
    (λ selectedAlgebra →
      Marked.LessEqual selectedAlgebra
        (Marked.operatorNorm selectedAlgebra
          (beforeStage replay domain term stage))
        (R407.ordinaryStageMajorant
          (R408.ordinaryPair (termReplay replay domain term)) stage))
    (termReplayUsesSelectedAlgebra replay domain term)
    (R408.beforeStageBelowTelescopeOrdinaryMajorant
      (termReplay replay domain term) stage)

afterStageBelowSelectedOrdinary :
  ∀ {Measure TestObservable dataSet extension base}
    (replay : SelectedCMP116R409TermReplay
      {Measure = Measure} {TestObservable = TestObservable}
      {dataSet = dataSet} {extension = extension} base) →
  ∀ domain term stage →
  Marked.LessEqual (operatorAlgebra replay)
    (Marked.operatorNorm (operatorAlgebra replay)
      (afterStage replay domain term stage))
    (R407.ordinaryStageMajorant
      (R408.ordinaryPair (termReplay replay domain term)) stage)
afterStageBelowSelectedOrdinary replay domain term stage =
  subst
    (λ selectedAlgebra →
      Marked.LessEqual selectedAlgebra
        (Marked.operatorNorm selectedAlgebra
          (afterStage replay domain term stage))
        (R407.ordinaryStageMajorant
          (R408.ordinaryPair (termReplay replay domain term)) stage))
    (termReplayUsesSelectedAlgebra replay domain term)
    (R408.afterStageBelowTelescopeOrdinaryMajorant
      (termReplay replay domain term) stage)

stageDifferenceBelowSelectedMarked :
  ∀ {Measure TestObservable dataSet extension base}
    (replay : SelectedCMP116R409TermReplay
      {Measure = Measure} {TestObservable = TestObservable}
      {dataSet = dataSet} {extension = extension} base) →
  ∀ domain term stage →
  Marked.LessEqual (operatorAlgebra replay)
    (Marked.operatorNorm (operatorAlgebra replay)
      (Marked.difference (operatorAlgebra replay)
        (beforeStage replay domain term stage)
        (afterStage replay domain term stage)))
    (R409.stageMarkedMajorant
      (termReplay replay domain term)
      (singleChangedAgreement replay domain term)
      stage)
stageDifferenceBelowSelectedMarked replay domain term stage =
  subst
    (λ selectedAlgebra →
      Marked.LessEqual selectedAlgebra
        (Marked.operatorNorm selectedAlgebra
          (Marked.difference selectedAlgebra
            (beforeStage replay domain term stage)
            (afterStage replay domain term stage)))
        (R409.stageMarkedMajorant
          (termReplay replay domain term)
          (singleChangedAgreement replay domain term)
          stage))
    (termReplayUsesSelectedAlgebra replay domain term)
    (R409.stageDifferenceBelowMarkedMajorant
      (termReplay replay domain term)
      (singleChangedAgreement replay domain term)
      stage)

compileSelectedTermwiseLocalization :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension} →
  SelectedCMP116R409TermReplay base →
  R406.SelectedCMP116TermwiseLocalization base
compileSelectedTermwiseLocalization replay = record
  { R406.SelectedCMP116TermwiseLocalization.selectedT5RGDensity =
      selectedT5RGDensity replay
  ; R406.SelectedCMP116TermwiseLocalization.selectedT5RGDensityIsBase =
      selectedT5RGDensityIsBase replay
  ; R406.SelectedCMP116TermwiseLocalization.leftObservable =
      leftObservable replay
  ; R406.SelectedCMP116TermwiseLocalization.rightObservable =
      rightObservable replay
  ; R406.SelectedCMP116TermwiseLocalization.leftJ = leftJ replay
  ; R406.SelectedCMP116TermwiseLocalization.rightJ = rightJ replay
  ; R406.SelectedCMP116TermwiseLocalization.leftJIsObservableIndexed =
      leftJIsObservableIndexed replay
  ; R406.SelectedCMP116TermwiseLocalization.rightJIsObservableIndexed =
      rightJIsObservableIndexed replay
  ; R406.SelectedCMP116TermwiseLocalization.DecouplingBoundaryAssignment =
      DecouplingBoundaryAssignment replay
  ; R406.SelectedCMP116TermwiseLocalization.selectedDecouplingBoundary =
      selectedDecouplingBoundary replay
  ; R406.SelectedCMP116TermwiseLocalization.Term = Term replay
  ; R406.SelectedCMP116TermwiseLocalization.Domain = Domain replay
  ; R406.SelectedCMP116TermwiseLocalization.Factor =
      R407.CMP109DerivativeStage
  ; R406.SelectedCMP116TermwiseLocalization.Operator = Operator replay
  ; R406.SelectedCMP116TermwiseLocalization.localizedDomains =
      localizedDomains replay
  ; R406.SelectedCMP116TermwiseLocalization.termsWithCommonY =
      termsWithCommonY replay
  ; R406.SelectedCMP116TermwiseLocalization.differentiatedTerm =
      differentiatedTerm replay
  ; R406.SelectedCMP116TermwiseLocalization.differentiatedTermMajorant =
      termMajorant replay
  ; R406.SelectedCMP116TermwiseLocalization.commonYBoundaryIntegrand =
      commonYBoundaryIntegrand replay
  ; R406.SelectedCMP116TermwiseLocalization.commonYShell =
      commonYShell replay
  ; R406.SelectedCMP116TermwiseLocalization.selectedBoundaryIntegrand =
      selectedBoundaryIntegrand replay
  ; R406.SelectedCMP116TermwiseLocalization.selectedConnectingShell =
      selectedConnectingShell replay
  ; R406.SelectedCMP116TermwiseLocalization.operatorAlgebra =
      operatorAlgebra replay
  ; R406.SelectedCMP116TermwiseLocalization.termFactors =
      λ domain term → R407.cmp109DerivativeStages
  ; R406.SelectedCMP116TermwiseLocalization.beforeOperator =
      beforeStage replay
  ; R406.SelectedCMP116TermwiseLocalization.afterOperator =
      afterStage replay
  ; R406.SelectedCMP116TermwiseLocalization.ordinaryFactorMajorant =
      λ domain term →
        R407.ordinaryStageMajorant
          (R408.ordinaryPair (termReplay replay domain term))
  ; R406.SelectedCMP116TermwiseLocalization.markedFactorMajorant =
      λ domain term →
        R409.stageMarkedMajorant
          (termReplay replay domain term)
          (singleChangedAgreement replay domain term)
  ; R406.SelectedCMP116TermwiseLocalization.differentiatedTermAbsoluteIsOperatorDifferenceNorm =
      differentiatedTermAbsoluteIsFourStageDifferenceNorm replay
  ; R406.SelectedCMP116TermwiseLocalization.differentiatedTermMajorantIsOperatorMarkedProduct =
      λ domain term → refl
  ; R406.SelectedCMP116TermwiseLocalization.beforeOperatorBelowOrdinary =
      beforeStageBelowSelectedOrdinary replay
  ; R406.SelectedCMP116TermwiseLocalization.afterOperatorBelowOrdinary =
      afterStageBelowSelectedOrdinary replay
  ; R406.SelectedCMP116TermwiseLocalization.markedOperatorDifferenceBelow =
      stageDifferenceBelowSelectedMarked replay
  ; R406.SelectedCMP116TermwiseLocalization.selectedBoundaryIsCommonYSum =
      selectedBoundaryIsCommonYSum replay
  ; R406.SelectedCMP116TermwiseLocalization.commonYBoundaryIsTermSum =
      commonYBoundaryIsTermSum replay
  ; R406.SelectedCMP116TermwiseLocalization.differentiatedMajorantsBelowCommonYShell =
      differentiatedMajorantsBelowCommonYShell replay
  ; R406.SelectedCMP116TermwiseLocalization.commonYShellsBelowSelectedConnectingShell =
      commonYShellsBelowSelectedConnectingShell replay
  }

selectedBoundaryLocalizationFromR409Replay :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension} →
  (replay : SelectedCMP116R409TermReplay base) →
  absℝ (selectedBoundaryIntegrand replay)
    ≤ℝ selectedConnectingShell replay
selectedBoundaryLocalizationFromR409Replay replay =
  R406.selectedBoundaryLocalizationFromR404R405
    (compileSelectedTermwiseLocalization replay)

round410R409ToR406FactorCompilerLevel : ProofLevel
round410R409ToR406FactorCompilerLevel = machineChecked

round410SelectedBoundaryCompilerLevel : ProofLevel
round410SelectedBoundaryCompilerLevel = machineChecked

-- The remaining fields are literal source/same-object semantics, not a fresh
-- operator inequality.
round410LiteralSourceScalarizationLevel : ProofLevel
round410LiteralSourceScalarizationLevel = conditional

round410CMP116PositiveSummationAttachmentLevel : ProofLevel
round410CMP116PositiveSummationAttachmentLevel = conditional
