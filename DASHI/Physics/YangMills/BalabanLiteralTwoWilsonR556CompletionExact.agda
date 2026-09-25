{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonR556CompletionExact where

------------------------------------------------------------------------
-- FAMILY-LEVEL COMPLETION:
--
-- literal twice-Wilson CMP116 theorem
--   -> exact embedded quarter-dyadic covariance bound
--   -> faithful Q->R order reflection
--   -> R556 on the canonical quarter-dyadic traversal shell.
--
-- The only scalar bridge retained is order reflection on the rational image.
-- This is foundational scalar transport, not Yang--Mills physics.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanCMP116R429MixedLogResponseRound445Exact as R445
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPhysicalSeparationRound450Exact as R450
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Ring
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonQuarterDyadicCompletionExact as Quarter
import DASHI.Physics.YangMills.BalabanCanonicalDyadicTraversalShellExact as DyadicShell
import DASHI.Physics.YangMills.BalabanLiteralWilsonMarkedLocalizationSourceExact as Downstream
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceRound556Exact as R556

record RationalImageOrderReflection
    (embedding : Ring.RationalRealRingEmbedding) : Set₁ where
  field
    reflectLessEqual :
      ∀ {left right : ℚ} →
      Quarter.embedQ embedding left
        ≤ℝ Quarter.embedQ embedding right →
      left ≤ right

open RationalImageOrderReflection public

record LiteralTwoWilsonQuarterDyadicFamily
    {Measure Observable : Set}
    (dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    (extension :
      R278.ScalarCovarianceConvergenceExtension dataSet)
    (base :
      R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (ringEmbedding : Ring.RationalRealRingEmbedding)
    : Set₂ where
  field
    physicalDistance :
      Observable → Observable → Nat

    dataAt :
      Nat → Observable → Observable →
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure}
        {TestObservable = Observable}
        {dataSet = dataSet}
        {extension = extension}
        base

    sourceAt :
      ∀ cutoff left right →
      Quarter.QuarterDyadicTwoWilsonSource
        {Measure = Measure}
        {Observable = Observable}
        {dataSet = dataSet}
        {extension = extension}
        {base = base}
        (dataAt cutoff left right)
        ringEmbedding

    leftObservableExact :
      ∀ cutoff left right →
      R444.leftObservable (dataAt cutoff left right) ≡ left

    rightObservableExact :
      ∀ cutoff left right →
      R444.rightObservable (dataAt cutoff left right) ≡ right

    cutoffExact :
      ∀ cutoff left right →
      R445.cutoff
        (Quarter.mixedLog (sourceAt cutoff left right))
      ≡ cutoff

    euclideanTimeExact :
      ∀ cutoff left right →
      R450.euclideanTime
        (Quarter.physical (sourceAt cutoff left right))
      ≡ physicalDistance left right

    orderReflection :
      RationalImageOrderReflection ringEmbedding

    downstream :
      Downstream.WilsonWEXTDownstreamSemantics dataSet

open LiteralTwoWilsonQuarterDyadicFamily public

finiteCovarianceBelowCanonicalDyadicShell :
  ∀ {Measure Observable dataSet extension base ringEmbedding}
    (family :
      LiteralTwoWilsonQuarterDyadicFamily
        {Measure = Measure}
        {Observable = Observable}
        dataSet extension base ringEmbedding)
    cutoff left right →
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    left right
  ≤
  DyadicShell.canonicalRootedShell
    (physicalDistance family left right)
finiteCovarianceBelowCanonicalDyadicShell
    {ringEmbedding = ringEmbedding}
    family cutoff left right =
  let
    source = sourceAt family cutoff left right

    embedded :
      Quarter.embedQ ringEmbedding
        (R278.connectedCovarianceMagnitude extension
          (Gram.measureSequence dataSet cutoff)
          left right)
      ≤ℝ
      Quarter.embedQ ringEmbedding
        (Shell.quarter
          * Geo.halfPower (physicalDistance family left right))
    embedded =
      subst
        (λ selectedCutoff →
          Quarter.embedQ ringEmbedding
            (R278.connectedCovarianceMagnitude extension
              (Gram.measureSequence dataSet selectedCutoff)
              left right)
          ≤ℝ
          Quarter.embedQ ringEmbedding
            (Shell.quarter
              * Geo.halfPower
                (physicalDistance family left right)))
        (cutoffExact family cutoff left right)
        (subst
          (λ selectedLeft →
            Quarter.embedQ ringEmbedding
              (R278.connectedCovarianceMagnitude extension
                (Gram.measureSequence dataSet
                  (R445.cutoff (Quarter.mixedLog source)))
                selectedLeft right)
            ≤ℝ
            Quarter.embedQ ringEmbedding
              (Shell.quarter
                * Geo.halfPower
                  (physicalDistance family left right)))
          (leftObservableExact family cutoff left right)
          (subst
            (λ selectedRight →
              Quarter.embedQ ringEmbedding
                (R278.connectedCovarianceMagnitude extension
                  (Gram.measureSequence dataSet
                    (R445.cutoff (Quarter.mixedLog source)))
                  (R444.leftObservable (dataAt family cutoff left right))
                  selectedRight)
              ≤ℝ
              Quarter.embedQ ringEmbedding
                (Shell.quarter
                  * Geo.halfPower
                    (physicalDistance family left right)))
            (rightObservableExact family cutoff left right)
            (subst
              (λ selectedTime →
                Quarter.embedQ ringEmbedding
                  (R278.connectedCovarianceMagnitude extension
                    (Gram.measureSequence dataSet
                      (R445.cutoff (Quarter.mixedLog source)))
                    (R444.leftObservable (dataAt family cutoff left right))
                    (R444.rightObservable (dataAt family cutoff left right)))
                ≤ℝ
                Quarter.embedQ ringEmbedding
                  (Shell.quarter * Geo.halfPower selectedTime))
              (euclideanTimeExact family cutoff left right)
              (Quarter.literalTwoWilsonEmbeddedQuarterDyadicDecay source))))
  in
  reflectLessEqual (orderReflection family) embedded

asR556 :
  ∀ {Measure Observable dataSet extension base ringEmbedding} →
  (family :
    LiteralTwoWilsonQuarterDyadicFamily
      {Measure = Measure}
      {Observable = Observable}
      dataSet extension base ringEmbedding) →
  R556.IndexedSourceFirstWilsonCovarianceData
    {Measure = Measure}
    {Observable = Observable}
    {Scale = Nat}
    {Volume = Nat}
    {Root = ⊤}
    dataSet extension
asR556 family = record
  { R556.IndexedSourceFirstWilsonCovarianceData.shellData =
      DyadicShell.canonicalTraversalShell
  ; R556.IndexedSourceFirstWilsonCovarianceData.scaleOfCutoff =
      λ cutoff → cutoff
  ; R556.IndexedSourceFirstWilsonCovarianceData.volumeOfCutoff =
      λ cutoff → cutoff
  ; R556.IndexedSourceFirstWilsonCovarianceData.physicalDistance =
      physicalDistance family
  ; R556.IndexedSourceFirstWilsonCovarianceData.connectingRoot =
      λ cutoff left right → tt
  ; R556.IndexedSourceFirstWilsonCovarianceData.timeTranslate =
      Downstream.timeTranslate (downstream family)
  ; R556.IndexedSourceFirstWilsonCovarianceData.finiteWilsonCovarianceBelowConnectingShell =
      finiteCovarianceBelowCanonicalDyadicShell family
  ; R556.IndexedSourceFirstWilsonCovarianceData.ConnectingClusterMeetsBothWilsonSupports =
      λ cutoff left right → ⊤
  ; R556.IndexedSourceFirstWilsonCovarianceData.leftBounded =
      Downstream.leftBounded (downstream family)
  ; R556.IndexedSourceFirstWilsonCovarianceData.translatedRightBounded =
      Downstream.translatedRightBounded (downstream family)
  ; R556.IndexedSourceFirstWilsonCovarianceData.translatedProductBounded =
      Downstream.translatedProductBounded (downstream family)
  ; R556.IndexedSourceFirstWilsonCovarianceData.supportDistanceIsEuclideanTime =
      Downstream.supportDistanceIsEuclideanTime
        (downstream family)
        (physicalDistance family)
  ; R556.IndexedSourceFirstWilsonCovarianceData.upperOrderClosed =
      Downstream.upperOrderClosed (downstream family)
  }
