{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonR413FourStageConstructorExact where

------------------------------------------------------------------------
-- R413-native construction of the literal R444 twice-Wilson carrier.
--
-- The source-faithful local object is CMP99PathDerivativeSourceReplay (R413):
-- it fixes the changed stage definitionally to the path/background derivative.
-- The older raw R444 constructor asked the physical caller to first manufacture
-- an R410 replay.  That is representation debt: R413.asR410CanonicalPathReplay
-- already performs exactly that compilation.
--
-- This owner therefore accepts R413 directly and constructs the existing
-- LiteralTwoWilsonRawFourStageSource.  The genuine source payments retained are
-- the differentiated scalar/scalarization, common-Y majorant, CMP116
-- (1.26)--(1.29) source data, and the common operator-algebra identification.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
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
import DASHI.Physics.YangMills.BalabanCMP99PathDerivativeSourceReplayRound413Exact as R413
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedSupportRound434Exact as R434
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonMarkedFibreConstructorExact as Fibre
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonCanonicalFourStageConstructorExact as Raw

record LiteralTwoWilsonR413FourStageSource
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

    -- Source-native path/background replacement theorem.
    sourceReplay :
      Domain → RawTerm → R413.CMP99PathDerivativeSourceReplay Operator ℝ

    rawDifferentiatedTerm : Domain → RawTerm → ℝ

    -- All selected terms are evaluated in one physical operator norm.
    operatorAlgebra : Marked.MarkedOperatorNormAlgebra Operator ℝ

    sourceReplayAlgebraIsOperatorAlgebra :
      ∀ domain raw →
      R413.telescopeAlgebra (sourceReplay domain raw)
      ≡ operatorAlgebra

    operatorOrderToReal : ∀ {lower upper} →
      Marked.LessEqual operatorAlgebra lower upper →
      lower ≤ℝ upper

    -- The genuinely source-specific scalarization theorem.  The four-stage
    -- replay itself is no longer supplied independently.
    rawDifferentiatedTermAbsoluteIsCanonicalProductDifferenceNorm :
      ∀ domain raw →
      let replay = R413.asR410CanonicalPathReplay (sourceReplay domain raw)
      in
      absℝ (rawDifferentiatedTerm domain raw)
      ≡
      Marked.operatorNorm operatorAlgebra
        (Marked.difference operatorAlgebra
          (Marked.operatorProduct operatorAlgebra
            (R407.stageOperator
              (R407.before
                (R408.ordinaryPair (R410.stageDifference replay))))
            R407.cmp109DerivativeStages)
          (Marked.operatorProduct operatorAlgebra
            (R407.stageOperator
              (R407.after
                (R408.ordinaryPair (R410.stageDifference replay))))
            R407.cmp109DerivativeStages))

    commonYShell : Domain → ℝ

    differentiatedMajorantsBelowCommonYShell :
      ∀ domain →
      Resum.sumℝ
        (λ term →
          let replay =
                R413.asR410CanonicalPathReplay
                  (sourceReplay domain (R434.rawTerm term))
          in
          Marked.markedProductMajorant operatorAlgebra
            (R407.ordinaryStageMajorant
              (R408.ordinaryPair (R410.stageDifference replay)))
            (R409.stageMarkedMajorant
              (R410.stageDifference replay)
              (R410.canonicalSingleChangedAgreement replay))
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

open LiteralTwoWilsonR413FourStageSource public

asRawFourStage :
  ∀ {Measure Observable dataSet extension base} →
  LiteralTwoWilsonR413FourStageSource
    {Measure = Measure} {Observable = Observable}
    {dataSet = dataSet} {extension = extension} base →
  Raw.LiteralTwoWilsonRawFourStageSource
    {Measure = Measure} {Observable = Observable}
    {dataSet = dataSet} {extension = extension} base
asRawFourStage input = record
  { Raw.LiteralTwoWilsonRawFourStageSource.leftObservable =
      leftObservable input
  ; Raw.LiteralTwoWilsonRawFourStageSource.rightObservable =
      rightObservable input
  ; Raw.LiteralTwoWilsonRawFourStageSource.leftJ =
      leftJ input
  ; Raw.LiteralTwoWilsonRawFourStageSource.rightJ =
      rightJ input
  ; Raw.LiteralTwoWilsonRawFourStageSource.leftJIsObservableIndexed =
      leftJIsObservableIndexed input
  ; Raw.LiteralTwoWilsonRawFourStageSource.rightJIsObservableIndexed =
      rightJIsObservableIndexed input
  ; Raw.LiteralTwoWilsonRawFourStageSource.leftMark =
      leftMark input
  ; Raw.LiteralTwoWilsonRawFourStageSource.rightMark =
      rightMark input
  ; Raw.LiteralTwoWilsonRawFourStageSource.RawTerm =
      RawTerm input
  ; Raw.LiteralTwoWilsonRawFourStageSource.Domain =
      Domain input
  ; Raw.LiteralTwoWilsonRawFourStageSource.Operator =
      Operator input
  ; Raw.LiteralTwoWilsonRawFourStageSource.CarriesLink =
      CarriesLink input
  ; Raw.LiteralTwoWilsonRawFourStageSource.rawFibre =
      rawFibre input
  ; Raw.LiteralTwoWilsonRawFourStageSource.localizedDomains =
      localizedDomains input
  ; Raw.LiteralTwoWilsonRawFourStageSource.DecouplingBoundaryAssignment =
      DecouplingBoundaryAssignment input
  ; Raw.LiteralTwoWilsonRawFourStageSource.selectedDecouplingBoundary =
      selectedDecouplingBoundary input
  ; Raw.LiteralTwoWilsonRawFourStageSource.rawDifferentiatedTerm =
      rawDifferentiatedTerm input
  ; Raw.LiteralTwoWilsonRawFourStageSource.operatorAlgebra =
      operatorAlgebra input
  ; Raw.LiteralTwoWilsonRawFourStageSource.operatorOrderToReal =
      operatorOrderToReal input
  ; Raw.LiteralTwoWilsonRawFourStageSource.rawCanonicalPathReplay =
      λ domain raw →
        R413.asR410CanonicalPathReplay (sourceReplay input domain raw)
  ; Raw.LiteralTwoWilsonRawFourStageSource.replayAlgebraIsOperatorAlgebra =
      λ domain raw →
        sourceReplayAlgebraIsOperatorAlgebra input domain raw
  ; Raw.LiteralTwoWilsonRawFourStageSource.rawDifferentiatedTermAbsoluteIsCanonicalProductDifferenceNorm =
      rawDifferentiatedTermAbsoluteIsCanonicalProductDifferenceNorm input
  ; Raw.LiteralTwoWilsonRawFourStageSource.commonYShell =
      commonYShell input
  ; Raw.LiteralTwoWilsonRawFourStageSource.differentiatedMajorantsBelowCommonYShell =
      differentiatedMajorantsBelowCommonYShell input
  ; Raw.LiteralTwoWilsonRawFourStageSource.selectedConnectingShell =
      selectedConnectingShell input
  ; Raw.LiteralTwoWilsonRawFourStageSource.commonYShellsBelowSelectedConnectingShell =
      commonYShellsBelowSelectedConnectingShell input
  ; Raw.LiteralTwoWilsonRawFourStageSource.source =
      source input
  ; Raw.LiteralTwoWilsonRawFourStageSource.sourceDomainsAreLiteralDomains =
      sourceDomainsAreLiteralDomains input
  ; Raw.LiteralTwoWilsonRawFourStageSource.sourceFixedYShellIsLiteralCommonYShell =
      sourceFixedYShellIsLiteralCommonYShell input
  }

asCanonicalTwiceMarkedFourStage :
  ∀ {Measure Observable dataSet extension base} →
  LiteralTwoWilsonR413FourStageSource
    {Measure = Measure} {Observable = Observable}
    {dataSet = dataSet} {extension = extension} base →
  R444.CanonicalTwiceMarkedFourStageData base
asCanonicalTwiceMarkedFourStage input =
  Raw.asCanonicalTwiceMarkedFourStage (asRawFourStage input)
