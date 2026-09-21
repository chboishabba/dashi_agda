{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalFourStageR406Round429Exact where

------------------------------------------------------------------------
-- B / ROUND429: BUILD R406 WITH THE R410 FOUR-STAGE FACTOR CARRIER
--
-- Preferred constructor eliminating the historical B1 post-hoc layout weld.
-- Factor is definitionally CMP109DerivativeStage and termFactors is
-- definitionally cmp109DerivativeStages.  Ordinary and marked factor bounds
-- are inherited from R408/R410.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact as Marked
import DASHI.Physics.YangMills.BalabanCMP109FourStageOperatorFactorRound407Exact as R407
import DASHI.Physics.YangMills.BalabanCMP99MarkedStageDifferenceRound408Exact as R408
import DASHI.Physics.YangMills.BalabanCMP99SingleMarkedFourStageRound409Exact as R409
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP116Round406ExactR410ReplayRound421Exact as R421

record CanonicalFourStageR406Data
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    : Set₁ where
  field
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

    operatorAlgebra : Marked.MarkedOperatorNormAlgebra Operator ℝ
    operatorOrderToReal : ∀ {lower upper} →
      Marked.LessEqual operatorAlgebra lower upper →
      lower ≤ℝ upper

    canonicalPathReplay :
      Domain → Term → R410.CanonicalPathMarkedCMP109Replay Operator ℝ

    replayAlgebraIsOperatorAlgebra :
      ∀ domain term →
      R408.telescopeAlgebra
        (R410.stageDifference (canonicalPathReplay domain term))
      ≡ operatorAlgebra

    differentiatedTermAbsoluteIsCanonicalProductDifferenceNorm :
      ∀ domain term →
      absℝ (differentiatedTerm domain term)
      ≡
      Marked.operatorNorm operatorAlgebra
        (Marked.difference operatorAlgebra
          (Marked.operatorProduct operatorAlgebra
            (R407.stageOperator
              (R407.before
                (R408.ordinaryPair
                  (R410.stageDifference
                    (canonicalPathReplay domain term)))))
            R407.cmp109DerivativeStages)
          (Marked.operatorProduct operatorAlgebra
            (R407.stageOperator
              (R407.after
                (R408.ordinaryPair
                  (R410.stageDifference
                    (canonicalPathReplay domain term)))))
            R407.cmp109DerivativeStages))

    selectedBoundaryIsCommonYSum :
      selectedBoundaryIntegrand ≡
      Resum.sumℝ commonYBoundaryIntegrand localizedDomains

    commonYBoundaryIsTermSum :
      ∀ domain →
      commonYBoundaryIntegrand domain ≡
      Resum.sumℝ (differentiatedTerm domain) (termsWithCommonY domain)

    differentiatedMajorantsBelowCommonYShell :
      ∀ domain →
      Resum.sumℝ
        (λ term →
          Marked.markedProductMajorant operatorAlgebra
            (R407.ordinaryStageMajorant
              (R408.ordinaryPair
                (R410.stageDifference (canonicalPathReplay domain term))))
            (R409.stageMarkedMajorant
              (R410.stageDifference (canonicalPathReplay domain term))
              (R410.canonicalSingleChangedAgreement
                (canonicalPathReplay domain term)))
            R407.cmp109DerivativeStages)
        (termsWithCommonY domain)
      ≤ℝ commonYShell domain

    commonYShellsBelowSelectedConnectingShell :
      Resum.sumℝ commonYShell localizedDomains
      ≤ℝ selectedConnectingShell

open CanonicalFourStageR406Data public

canonicalApplication :
  ∀ {Measure TestObservable dataSet extension}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension} →
  CanonicalFourStageR406Data
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} base →
  R406.SelectedCMP116TermwiseLocalization base
canonicalApplication data = record
  { R406.SelectedCMP116TermwiseLocalization.selectedT5RGDensity =
      R318.SourceDirection _
  ; R406.SelectedCMP116TermwiseLocalization.selectedT5RGDensityIsBase = refl
  ; R406.SelectedCMP116TermwiseLocalization.leftObservable =
      leftObservable data
  ; R406.SelectedCMP116TermwiseLocalization.rightObservable =
      rightObservable data
  ; R406.SelectedCMP116TermwiseLocalization.leftJ = leftJ data
  ; R406.SelectedCMP116TermwiseLocalization.rightJ = rightJ data
  ; R406.SelectedCMP116TermwiseLocalization.leftJIsObservableIndexed =
      leftJIsObservableIndexed data
  ; R406.SelectedCMP116TermwiseLocalization.rightJIsObservableIndexed =
      rightJIsObservableIndexed data
  ; R406.SelectedCMP116TermwiseLocalization.DecouplingBoundaryAssignment =
      DecouplingBoundaryAssignment data
  ; R406.SelectedCMP116TermwiseLocalization.selectedDecouplingBoundary =
      selectedDecouplingBoundary data
  ; R406.SelectedCMP116TermwiseLocalization.Term = Term data
  ; R406.SelectedCMP116TermwiseLocalization.Domain = Domain data
  ; R406.SelectedCMP116TermwiseLocalization.Factor = R407.CMP109DerivativeStage
  ; R406.SelectedCMP116TermwiseLocalization.Operator = Operator data
  ; R406.SelectedCMP116TermwiseLocalization.localizedDomains =
      localizedDomains data
  ; R406.SelectedCMP116TermwiseLocalization.termsWithCommonY =
      termsWithCommonY data
  ; R406.SelectedCMP116TermwiseLocalization.differentiatedTerm =
      differentiatedTerm data
  ; R406.SelectedCMP116TermwiseLocalization.differentiatedTermMajorant =
      λ domain term →
        Marked.markedProductMajorant (operatorAlgebra data)
          (R407.ordinaryStageMajorant
            (R408.ordinaryPair
              (R410.stageDifference (canonicalPathReplay data domain term))))
          (R409.stageMarkedMajorant
            (R410.stageDifference (canonicalPathReplay data domain term))
            (R410.canonicalSingleChangedAgreement
              (canonicalPathReplay data domain term)))
          R407.cmp109DerivativeStages
  ; R406.SelectedCMP116TermwiseLocalization.commonYBoundaryIntegrand =
      commonYBoundaryIntegrand data
  ; R406.SelectedCMP116TermwiseLocalization.commonYShell = commonYShell data
  ; R406.SelectedCMP116TermwiseLocalization.selectedBoundaryIntegrand =
      selectedBoundaryIntegrand data
  ; R406.SelectedCMP116TermwiseLocalization.selectedConnectingShell =
      selectedConnectingShell data
  ; R406.SelectedCMP116TermwiseLocalization.operatorAlgebra =
      operatorAlgebra data
  ; R406.SelectedCMP116TermwiseLocalization.operatorOrderToReal =
      operatorOrderToReal data
  ; R406.SelectedCMP116TermwiseLocalization.termFactors =
      λ _ _ → R407.cmp109DerivativeStages
  ; R406.SelectedCMP116TermwiseLocalization.beforeOperator =
      λ domain term →
        R407.stageOperator
          (R407.before
            (R408.ordinaryPair
              (R410.stageDifference (canonicalPathReplay data domain term))))
  ; R406.SelectedCMP116TermwiseLocalization.afterOperator =
      λ domain term →
        R407.stageOperator
          (R407.after
            (R408.ordinaryPair
              (R410.stageDifference (canonicalPathReplay data domain term))))
  ; R406.SelectedCMP116TermwiseLocalization.ordinaryFactorMajorant =
      λ domain term →
        R407.ordinaryStageMajorant
          (R408.ordinaryPair
            (R410.stageDifference (canonicalPathReplay data domain term)))
  ; R406.SelectedCMP116TermwiseLocalization.markedFactorMajorant =
      λ domain term →
        R409.stageMarkedMajorant
          (R410.stageDifference (canonicalPathReplay data domain term))
          (R410.canonicalSingleChangedAgreement
            (canonicalPathReplay data domain term))
  ; R406.SelectedCMP116TermwiseLocalization.differentiatedTermAbsoluteIsOperatorDifferenceNorm =
      differentiatedTermAbsoluteIsCanonicalProductDifferenceNorm data
  ; R406.SelectedCMP116TermwiseLocalization.differentiatedTermMajorantIsOperatorMarkedProduct =
      λ _ _ → refl
  ; R406.SelectedCMP116TermwiseLocalization.beforeOperatorBelowOrdinary =
      λ domain term stage →
        subst
          (λ algebra →
            Marked.LessEqual algebra
              (Marked.operatorNorm algebra
                (R407.stageOperator
                  (R407.before
                    (R408.ordinaryPair
                      (R410.stageDifference
                        (canonicalPathReplay data domain term))))
                  stage))
              (R407.ordinaryStageMajorant
                (R408.ordinaryPair
                  (R410.stageDifference
                    (canonicalPathReplay data domain term)))
                stage))
          (replayAlgebraIsOperatorAlgebra data domain term)
          (R408.beforeStageBelowTelescopeOrdinaryMajorant
            (R410.stageDifference (canonicalPathReplay data domain term))
            stage)
  ; R406.SelectedCMP116TermwiseLocalization.afterOperatorBelowOrdinary =
      λ domain term stage →
        subst
          (λ algebra →
            Marked.LessEqual algebra
              (Marked.operatorNorm algebra
                (R407.stageOperator
                  (R407.after
                    (R408.ordinaryPair
                      (R410.stageDifference
                        (canonicalPathReplay data domain term))))
                  stage))
              (R407.ordinaryStageMajorant
                (R408.ordinaryPair
                  (R410.stageDifference
                    (canonicalPathReplay data domain term)))
                stage))
          (replayAlgebraIsOperatorAlgebra data domain term)
          (R408.afterStageBelowTelescopeOrdinaryMajorant
            (R410.stageDifference (canonicalPathReplay data domain term))
            stage)
  ; R406.SelectedCMP116TermwiseLocalization.markedOperatorDifferenceBelow =
      λ domain term stage →
        subst
          (λ algebra →
            Marked.LessEqual algebra
              (Marked.operatorNorm algebra
                (Marked.difference algebra
                  (R407.stageOperator
                    (R407.before
                      (R408.ordinaryPair
                        (R410.stageDifference
                          (canonicalPathReplay data domain term))))
                    stage)
                  (R407.stageOperator
                    (R407.after
                      (R408.ordinaryPair
                        (R410.stageDifference
                          (canonicalPathReplay data domain term))))
                    stage)))
              (R409.stageMarkedMajorant
                (R410.stageDifference
                  (canonicalPathReplay data domain term))
                (R410.canonicalSingleChangedAgreement
                  (canonicalPathReplay data domain term))
                stage))
          (replayAlgebraIsOperatorAlgebra data domain term)
          (R409.stageDifferenceBelowMarkedMajorant
            (R410.stageDifference (canonicalPathReplay data domain term))
            (R410.canonicalSingleChangedAgreement
              (canonicalPathReplay data domain term))
            stage)
  ; R406.SelectedCMP116TermwiseLocalization.selectedBoundaryIsCommonYSum =
      selectedBoundaryIsCommonYSum data
  ; R406.SelectedCMP116TermwiseLocalization.commonYBoundaryIsTermSum =
      commonYBoundaryIsTermSum data
  ; R406.SelectedCMP116TermwiseLocalization.differentiatedMajorantsBelowCommonYShell =
      differentiatedMajorantsBelowCommonYShell data
  ; R406.SelectedCMP116TermwiseLocalization.commonYShellsBelowSelectedConnectingShell =
      commonYShellsBelowSelectedConnectingShell data
  }

canonicalOperatorReplay :
  ∀ {Measure TestObservable dataSet extension}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (data :
      CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base) →
  R421.LiteralRound406R410OperatorReplay (canonicalApplication data)
canonicalOperatorReplay data = record
  { R421.LiteralRound406R410OperatorReplay.canonicalPathReplay =
      canonicalPathReplay data
  ; R421.LiteralRound406R410OperatorReplay.r406ProductNormIsCanonicalR410ProductNorm =
      λ domain term →
        cong
          (λ algebra →
            Marked.operatorNorm algebra
              (Marked.difference algebra
                (Marked.operatorProduct algebra
                  (R407.stageOperator
                    (R407.before
                      (R408.ordinaryPair
                        (R410.stageDifference
                          (canonicalPathReplay data domain term)))))
                  R407.cmp109DerivativeStages)
                (Marked.operatorProduct algebra
                  (R407.stageOperator
                    (R407.after
                      (R408.ordinaryPair
                        (R410.stageDifference
                          (canonicalPathReplay data domain term)))))
                  R407.cmp109DerivativeStages)))
          (sym (replayAlgebraIsOperatorAlgebra data domain term))
  ; R421.LiteralRound406R410OperatorReplay.r406MajorantIsCanonicalR410Majorant =
      λ domain term →
        cong
          (λ algebra →
            Marked.markedProductMajorant algebra
              (R407.ordinaryStageMajorant
                (R408.ordinaryPair
                  (R410.stageDifference
                    (canonicalPathReplay data domain term))))
              (R409.stageMarkedMajorant
                (R410.stageDifference
                  (canonicalPathReplay data domain term))
                (R410.canonicalSingleChangedAgreement
                  (canonicalPathReplay data domain term)))
              R407.cmp109DerivativeStages)
          (sym (replayAlgebraIsOperatorAlgebra data domain term))
  }

round429CanonicalR406FourStageCompilerLevel : ProofLevel
round429CanonicalR406FourStageCompilerLevel = machineChecked

round429SeparateB1LayoutAttachmentRequired : ProofLevel
round429SeparateB1LayoutAttachmentRequired = machineChecked

-- On this preferred constructor B1 is gone.  The remaining source theorem is
-- the actual scalarization of the differentiated CMP116 term together with the
-- canonical path replay/source data themselves.
literalRound429CanonicalSelectedTermSourceLevel : ProofLevel
literalRound429CanonicalSelectedTermSourceLevel = conditional
