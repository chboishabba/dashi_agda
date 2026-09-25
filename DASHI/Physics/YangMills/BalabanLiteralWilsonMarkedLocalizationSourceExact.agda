{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralWilsonMarkedLocalizationSourceExact where

------------------------------------------------------------------------
-- Literal Wilson W1/W3 source-native theorem package.
--
-- This is the irreducible analytic surface after the compiler reductions in
-- BalabanWilsonMarkedClusterDifferentiationExact and
-- BalabanLiteralWilsonWEXTTheoremExact.
--
-- W1 source mathematics:
--   * an actual source-dependent Wilson marked cluster expansion;
--   * ordinary mixed differentiation on one common analytic neighbourhood;
--   * locality of cluster terms with respect to the two Wilson supports;
--   * equality of that mixed derivative with the normalized Wilson response.
--
-- W3 source mathematics:
--   * pointwise absolute localization of each retained two-support cluster;
--   * the source/rooted-shell accounting for those local charges.
--
-- The record deliberately does NOT identify Wilson cluster weights with the
-- historical generic extensionActivity carrier and does NOT identify Wilson
-- observables with Balaban's printed bond-valued J by fiat.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣; _≤_)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.YangMillsRationalAbsoluteCovarianceExtensionRound575Exact as R575
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonMixedLogCovarianceRound573Exact as R573
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceRound556Exact as R556
import DASHI.Physics.YangMills.BalabanWilsonMarkedClusterDifferentiationExact as Diff
import DASHI.Physics.YangMills.BalabanLiteralWilsonWEXTTheoremExact as WEXT

record LiteralWilsonMarkedLocalizationSource
    {Measure Observable Scale Volume Root Source Cluster : Set}
    (dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    (laws :
      R575.RationalCovarianceContinuityLaws dataSet)
    : Set₂ where
  field
    --------------------------------------------------------------------
    -- W1: literal Wilson marked analytic expansion.
    --------------------------------------------------------------------
    sourceCalculus :
      ∀ cutoff →
      Cumulant.NormalizedLogSourceCalculus
        (R573.r278MomentAlgebra
          (R575.rationalAbsoluteCovarianceExtension laws)
          (Gram.measureSequence dataSet cutoff))

    derivativeCalculus :
      Nat → Observable → Observable →
      Diff.MixedSourceDerivativeCalculus Source

    derivativeVanishing :
      ∀ cutoff left right →
      Diff.MixedSourceDerivativeVanishing
        (derivativeCalculus cutoff left right)

    markedExpansion :
      ∀ cutoff left right →
      Diff.SupportIndexedMarkedClusterExpansion
        Source Cluster
        (derivativeCalculus cutoff left right)

    normalizedWilsonResponseIsMarkedMixedDerivative :
      ∀ cutoff left right →
      Cumulant.mixedSecondLogDerivative
        (sourceCalculus cutoff)
        left right
      ≡
      Diff.mixedDerivative
        (derivativeCalculus cutoff left right)
        (Diff.logPartition (markedExpansion cutoff left right))

    --------------------------------------------------------------------
    -- Shared physical geometry.
    --------------------------------------------------------------------
    shellData :
      Shell.TraversalShellData Scale Volume Root

    scaleOfCutoff : Nat → Scale
    volumeOfCutoff : Nat → Volume

    physicalDistance : Observable → Observable → Nat
    connectingRoot : Nat → Observable → Observable → Root

    ConnectingClusterMeetsBothSupports :
      Nat → Observable → Observable → Set

    --------------------------------------------------------------------
    -- W3: pointwise marked localization + rooted charge accounting.
    --------------------------------------------------------------------
    shellCharge :
      Nat → Observable → Observable → Cluster → ℚ

    pointwiseWilsonClusterLocalization :
      ∀ cutoff left right cluster →
      let expansion = markedExpansion cutoff left right in
      ∣ Diff.mixedDerivative
          (derivativeCalculus cutoff left right)
          (Diff.clusterTerm expansion cluster) ∣
      ≤ shellCharge cutoff left right cluster

    localizedShellChargeSum :
      ∀ cutoff left right →
      let expansion = markedExpansion cutoff left right
          locality = Diff.supportLocality expansion
      in
      TwoMark.sumℚ
        (TwoMark.map
          (shellCharge cutoff left right)
          (Diff.filterTwoSupport
            (Diff.touchesLeft locality)
            (Diff.touchesRight locality)
            (Diff.clusters expansion)))
      ≤
      Shell.rootedShell shellData
        (scaleOfCutoff cutoff)
        (volumeOfCutoff cutoff)
        (connectingRoot cutoff left right)
        (physicalDistance left right)

open LiteralWilsonMarkedLocalizationSource public

record WilsonWEXTDownstreamSemantics
    {Measure Observable : Set}
    (dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    : Set₁ where
  field
    timeTranslate : Observable → Nat → Observable

    leftBounded :
      ∀ observable →
      Gram.BoundedObservable dataSet observable

    translatedRightBounded :
      ∀ observable time →
      Gram.BoundedObservable dataSet (timeTranslate observable time)

    translatedProductBounded :
      ∀ left right time →
      Gram.BoundedObservable dataSet
        (Gram.multiplyObservable (Gram.operations dataSet)
          left (timeTranslate right time))

    supportDistanceIsEuclideanTime :
      (physicalDistance : Observable → Observable → Nat) →
      ∀ left right time →
      physicalDistance left (timeTranslate right time) ≡ time

    upperOrderClosed :
      ∀ sequence target upper →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper

open WilsonWEXTDownstreamSemantics public

literalMarkedLocalizationCompilesToR556 :
  ∀ {Measure Observable Scale Volume Root Source Cluster dataSet laws}
    (source :
      LiteralWilsonMarkedLocalizationSource
        {Measure = Measure}
        {Observable = Observable}
        {Scale = Scale}
        {Volume = Volume}
        {Root = Root}
        {Source = Source}
        {Cluster = Cluster}
        dataSet laws)
    (semantics :
      WilsonWEXTDownstreamSemantics dataSet) →
  R556.IndexedSourceFirstWilsonCovarianceData
    {Measure = Measure}
    {Observable = Observable}
    {Scale = Scale}
    {Volume = Volume}
    {Root = Root}
    dataSet
    (R575.rationalAbsoluteCovarianceExtension laws)
literalMarkedLocalizationCompilesToR556 source semantics =
  WEXT.literalWilsonCovarianceSourceFromObservableIndexedMarkedLocalization
    (sourceCalculus source)
    (derivativeCalculus source)
    (derivativeVanishing source)
    (markedExpansion source)
    (normalizedWilsonResponseIsMarkedMixedDerivative source)
    (shellData source)
    (scaleOfCutoff source)
    (volumeOfCutoff source)
    (physicalDistance source)
    (connectingRoot source)
    (ConnectingClusterMeetsBothSupports source)
    (shellCharge source)
    (pointwiseWilsonClusterLocalization source)
    (localizedShellChargeSum source)
    (timeTranslate semantics)
    (leftBounded semantics)
    (translatedRightBounded semantics)
    (translatedProductBounded semantics)
    (supportDistanceIsEuclideanTime semantics (physicalDistance source))
    (upperOrderClosed semantics)

------------------------------------------------------------------------
-- Status boundary.
------------------------------------------------------------------------

literalWilsonMarkedExpansionAndDifferentiationLevel : Set
literalWilsonMarkedExpansionAndDifferentiationLevel =
  LiteralWilsonMarkedLocalizationSource _

-- No ProofLevel promotion is attached here: inhabiting the record is the actual
-- analytic theorem payment.  The compiler theorem above is ordinary Agda.
