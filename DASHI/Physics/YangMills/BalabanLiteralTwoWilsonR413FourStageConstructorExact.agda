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
asRawFourStage source = record
  { Raw.LiteralTwoWilsonRawFourStageSource.leftObservable =
      leftObservable source
  ; Raw.LiteralTwoWilsonRawFourStageSource.rightObservable =
      rightObservable source
  ; Raw.LiteralTwoWilsonRawFourStageSource.leftJ =
      leftJ source
  ; Raw.LiteralTwoWilsonRawFourStageSource.rightJ =
      rightJ source
  ; Raw.LiteralTwoWilsonRawFourStageSource.leftJIsObservableIndexed =
      leftJIsObservableIndexed source
  ; Raw.LiteralTwoWilsonRawFourStageSource.rightJIsObservableIndexed =
      rightJIsObservableIndexed source
  ; Raw.LiteralTwoWilsonRawFourStageSource.leftMark =
      leftMark source
  ; Raw.LiteralTwoWilsonRawFourStageSource.rightMark =
      rightMark source
  ; Raw.LiteralTwoWilsonRawFourStageSource.RawTerm =
      RawTerm source
  ; Raw.LiteralTwoWilsonRawFourStageSource.Domain =
      Domain source
  ; Raw.LiteralTwoWilsonRawFourStageSource.Operator =
      Operator source
  ; Raw.LiteralTwoWilsonRawFourStageSource.CarriesLink =
      CarriesLink source
  ; Raw.LiteralTwoWilsonRawFourStageSource.rawFibre =
      rawFibre source
  ; Raw.LiteralTwoWilsonRawFourStageSource.localizedDomains =
      localizedDomains source
  ; Raw.LiteralTwoWilsonRawFourStageSource.DecouplingBoundaryAssignment =
      DecouplingBoundaryAssignment source
  ; Raw.LiteralTwoWilsonRawFourStageSource.selectedDecouplingBoundary =
      selectedDecouplingBoundary source
  ; Raw.LiteralTwoWilsonRawFourStageSource.rawDifferentiatedTerm =
      rawDifferentiatedTerm source
  ; Raw.LiteralTwoWilsonRawFourStageSource.operatorAlgebra =
      operatorAlgebra source
  ; Raw.LiteralTwoWilsonRawFourStageSource.operatorOrderToReal =
      operatorOrderToReal source
  ; Raw.LiteralTwoWilsonRawFourStageSource.rawCanonicalPathReplay =
      λ domain raw →
        R413.asR410CanonicalPathReplay (sourceReplay source domain raw)
  ; Raw.LiteralTwoWilsonRawFourStageSource.replayAlgebraIsOperatorAlgebra =
      λ domain raw →
        sourceReplayAlgebraIsOperatorAlgebra source domain raw
  ; Raw.LiteralTwoWilsonRawFourStageSource.rawDifferentiatedTermAbsoluteIsCanonicalProductDifferenceNorm =
      rawDifferentiatedTermAbsoluteIsCanonicalProductDifferenceNorm source
  ; Raw.LiteralTwoWilsonRawFourStageSource.commonYShell =
      commonYShell source
  ; Raw.LiteralTwoWilsonRawFourStageSource.differentiatedMajorantsBelowCommonYShell =
      differentiatedMajorantsBelowCommonYShell source
  ; Raw.LiteralTwoWilsonRawFourStageSource.selectedConnectingShell =
      selectedConnectingShell source
  ; Raw.LiteralTwoWilsonRawFourStageSource.commonYShellsBelowSelectedConnectingShell =
      commonYShellsBelowSelectedConnectingShell source
  ; Raw.LiteralTwoWilsonRawFourStageSource.source =
      source source
  ; Raw.LiteralTwoWilsonRawFourStageSource.sourceDomainsAreLiteralDomains =
      sourceDomainsAreLiteralDomains source
  ; Raw.LiteralTwoWilsonRawFourStageSource.sourceFixedYShellIsLiteralCommonYShell =
      sourceFixedYShellIsLiteralCommonYShell source
  }

asCanonicalTwiceMarkedFourStage :
  ∀ {Measure Observable dataSet extension base} →
  LiteralTwoWilsonR413FourStageSource
    {Measure = Measure} {Observable = Observable}
    {dataSet = dataSet} {extension = extension} base →
  R444.CanonicalTwiceMarkedFourStageData base
asCanonicalTwiceMarkedFourStage source =
  Raw.asCanonicalTwiceMarkedFourStage (asRawFourStage source)
