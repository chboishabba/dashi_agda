{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonCanonicalFourStageConstructorExact where

------------------------------------------------------------------------
-- Canonical construction of the R444 literal twice-Wilson four-stage carrier.
--
-- Two pieces of bookkeeping are made definitional here:
--
--   commonYBoundary(Y) = sum_{term in selected fibre Y} differentiatedTerm(Y,term)
--   selectedBoundary   = sum_Y commonYBoundary(Y)
--
-- The twice-marked term carrier itself is generated from the raw common-Y
-- fibre by BalabanLiteralTwoWilsonMarkedFibreConstructorExact.  Consequently:
--
--   * both Wilson/source marks are structural;
--   * every retained fibre is structurally nonempty;
--   * the two finite expansion equalities are refl.
--
-- The remaining inputs are exactly source mathematics: the raw differentiated
-- term/scalarization and R410 replay, its positive common-Y majorant, the
-- source CMP116 (1.26)--(1.29) data, and the outer shell estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ; _≤ℝ_)

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
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
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedSupportRound434Exact as R434
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonMarkedFibreConstructorExact as Fibre

record LiteralTwoWilsonRawFourStageSource
    {Measure Observable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
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

    leftMark rightMark : Support.Link

    RawTerm Domain Operator : Set
    CarriesLink : RawTerm → Support.Link → Set

    rawFibre :
      Fibre.RawTwoWilsonFibre
        Domain RawTerm CarriesLink leftMark rightMark

    localizedDomains : List Domain

    DecouplingBoundaryAssignment : Set
    selectedDecouplingBoundary : DecouplingBoundaryAssignment

    rawDifferentiatedTerm : Domain → RawTerm → ℝ

    operatorAlgebra : Marked.MarkedOperatorNormAlgebra Operator ℝ
    operatorOrderToReal : ∀ {lower upper} →
      Marked.LessEqual operatorAlgebra lower upper →
      lower ≤ℝ upper

    rawCanonicalPathReplay :
      Domain → RawTerm →
      R410.CanonicalPathMarkedCMP109Replay Operator ℝ

    replayAlgebraIsOperatorAlgebra :
      ∀ domain raw →
      R408.telescopeAlgebra
        (R410.stageDifference (rawCanonicalPathReplay domain raw))
      ≡ operatorAlgebra

    rawDifferentiatedTermAbsoluteIsCanonicalProductDifferenceNorm :
      ∀ domain raw →
      absℝ (rawDifferentiatedTerm domain raw)
      ≡
      Marked.operatorNorm operatorAlgebra
        (Marked.difference operatorAlgebra
          (Marked.operatorProduct operatorAlgebra
            (R407.stageOperator
              (R407.before
                (R408.ordinaryPair
                  (R410.stageDifference
                    (rawCanonicalPathReplay domain raw)))))
            R407.cmp109DerivativeStages)
          (Marked.operatorProduct operatorAlgebra
            (R407.stageOperator
              (R407.after
                (R408.ordinaryPair
                  (R410.stageDifference
                    (rawCanonicalPathReplay domain raw)))))
            R407.cmp109DerivativeStages))

    commonYShell : Domain → ℝ

    differentiatedMajorantsBelowCommonYShell :
      ∀ domain →
      Resum.sumℝ
        (λ term →
          Marked.markedProductMajorant operatorAlgebra
            (R407.ordinaryStageMajorant
              (R408.ordinaryPair
                (R410.stageDifference
                  (rawCanonicalPathReplay domain (R434.rawTerm term)))))
            (R409.stageMarkedMajorant
              (R410.stageDifference
                (rawCanonicalPathReplay domain (R434.rawTerm term)))
              (R410.canonicalSingleChangedAgreement
                (rawCanonicalPathReplay domain (R434.rawTerm term))))
            R407.cmp109DerivativeStages)
        (Fibre.markedTerms rawFibre domain)
      ≤ℝ commonYShell domain

    selectedConnectingShell : ℝ

    commonYShellsBelowSelectedConnectingShell :
      Resum.sumℝ commonYShell localizedDomains
      ≤ℝ selectedConnectingShell

    source : Source.PublishedCMP116Equation126129RateSplit Domain

    sourceDomainsAreLiteralDomains :
      Source.localizedDomains source ≡ localizedDomains

    sourceFixedYShellIsLiteralCommonYShell :
      ∀ domain →
      Source.fixedYShell source domain ≡ commonYShell domain

open LiteralTwoWilsonRawFourStageSource public

markedDifferentiatedTerm :
  ∀ {Measure Observable dataSet extension base}
    (raw :
      LiteralTwoWilsonRawFourStageSource
        {Measure = Measure} {Observable = Observable}
        {dataSet = dataSet} {extension = extension} base) →
  Domain raw →
  R434.TwiceMarkedTerm
    (RawTerm raw)
    (CarriesLink raw)
    (leftMark raw)
    (rightMark raw) →
  ℝ
markedDifferentiatedTerm raw domain term =
  rawDifferentiatedTerm raw domain (R434.rawTerm term)

commonYBoundary :
  ∀ {Measure Observable dataSet extension base}
    (raw :
      LiteralTwoWilsonRawFourStageSource
        {Measure = Measure} {Observable = Observable}
        {dataSet = dataSet} {extension = extension} base) →
  Domain raw → ℝ
commonYBoundary raw domain =
  Resum.sumℝ
    (markedDifferentiatedTerm raw domain)
    (Fibre.markedTerms (rawFibre raw) domain)

selectedBoundary :
  ∀ {Measure Observable dataSet extension base}
    (raw :
      LiteralTwoWilsonRawFourStageSource
        {Measure = Measure} {Observable = Observable}
        {dataSet = dataSet} {extension = extension} base) →
  ℝ
selectedBoundary raw =
  Resum.sumℝ (commonYBoundary raw) (localizedDomains raw)

asCanonicalTwiceMarkedFourStage :
  ∀ {Measure Observable dataSet extension}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension} →
  (raw :
    LiteralTwoWilsonRawFourStageSource
      {Measure = Measure} {Observable = Observable}
      {dataSet = dataSet} {extension = extension} base) →
  R444.CanonicalTwiceMarkedFourStageData base
asCanonicalTwiceMarkedFourStage raw = record
  { R444.CanonicalTwiceMarkedFourStageData.leftObservable =
      leftObservable raw
  ; R444.CanonicalTwiceMarkedFourStageData.rightObservable =
      rightObservable raw
  ; R444.CanonicalTwiceMarkedFourStageData.leftJ =
      leftJ raw
  ; R444.CanonicalTwiceMarkedFourStageData.rightJ =
      rightJ raw
  ; R444.CanonicalTwiceMarkedFourStageData.leftJIsObservableIndexed =
      leftJIsObservableIndexed raw
  ; R444.CanonicalTwiceMarkedFourStageData.rightJIsObservableIndexed =
      rightJIsObservableIndexed raw
  ; R444.CanonicalTwiceMarkedFourStageData.leftMark =
      leftMark raw
  ; R444.CanonicalTwiceMarkedFourStageData.rightMark =
      rightMark raw
  ; R444.CanonicalTwiceMarkedFourStageData.RawTerm =
      RawTerm raw
  ; R444.CanonicalTwiceMarkedFourStageData.CarriesLink =
      CarriesLink raw
  ; R444.CanonicalTwiceMarkedFourStageData.DecouplingBoundaryAssignment =
      DecouplingBoundaryAssignment raw
  ; R444.CanonicalTwiceMarkedFourStageData.selectedDecouplingBoundary =
      selectedDecouplingBoundary raw
  ; R444.CanonicalTwiceMarkedFourStageData.Domain =
      Domain raw
  ; R444.CanonicalTwiceMarkedFourStageData.Operator =
      Operator raw
  ; R444.CanonicalTwiceMarkedFourStageData.localizedDomains =
      localizedDomains raw
  ; R444.CanonicalTwiceMarkedFourStageData.selectedHead =
      Fibre.markedHead (rawFibre raw)
  ; R444.CanonicalTwiceMarkedFourStageData.selectedTail =
      Fibre.markedTail (rawFibre raw)
  ; R444.CanonicalTwiceMarkedFourStageData.differentiatedTerm =
      markedDifferentiatedTerm raw
  ; R444.CanonicalTwiceMarkedFourStageData.commonYBoundaryIntegrand =
      commonYBoundary raw
  ; R444.CanonicalTwiceMarkedFourStageData.commonYShell =
      commonYShell raw
  ; R444.CanonicalTwiceMarkedFourStageData.selectedBoundaryIntegrand =
      selectedBoundary raw
  ; R444.CanonicalTwiceMarkedFourStageData.selectedConnectingShell =
      selectedConnectingShell raw
  ; R444.CanonicalTwiceMarkedFourStageData.operatorAlgebra =
      operatorAlgebra raw
  ; R444.CanonicalTwiceMarkedFourStageData.operatorOrderToReal =
      operatorOrderToReal raw
  ; R444.CanonicalTwiceMarkedFourStageData.canonicalPathReplay =
      λ domain term →
        rawCanonicalPathReplay raw domain (R434.rawTerm term)
  ; R444.CanonicalTwiceMarkedFourStageData.replayAlgebraIsOperatorAlgebra =
      λ domain term →
        replayAlgebraIsOperatorAlgebra raw domain (R434.rawTerm term)
  ; R444.CanonicalTwiceMarkedFourStageData.differentiatedTermAbsoluteIsCanonicalProductDifferenceNorm =
      λ domain term →
        rawDifferentiatedTermAbsoluteIsCanonicalProductDifferenceNorm
          raw domain (R434.rawTerm term)
  ; R444.CanonicalTwiceMarkedFourStageData.selectedBoundaryIsCommonYSum =
      refl
  ; R444.CanonicalTwiceMarkedFourStageData.commonYBoundaryIsTermSum =
      λ domain → refl
  ; R444.CanonicalTwiceMarkedFourStageData.differentiatedMajorantsBelowCommonYShell =
      differentiatedMajorantsBelowCommonYShell raw
  ; R444.CanonicalTwiceMarkedFourStageData.commonYShellsBelowSelectedConnectingShell =
      commonYShellsBelowSelectedConnectingShell raw
  ; R444.CanonicalTwiceMarkedFourStageData.source =
      source raw
  ; R444.CanonicalTwiceMarkedFourStageData.sourceDomainsAreLiteralDomains =
      sourceDomainsAreLiteralDomains raw
  ; R444.CanonicalTwiceMarkedFourStageData.sourceFixedYShellIsLiteralCommonYShell =
      sourceFixedYShellIsLiteralCommonYShell raw
  }
