{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsPreferredWilsonWEXTSourceRound576Exact where

------------------------------------------------------------------------
-- GOAL-1 B1 / ROUND576:
-- PREFERRED WEXT SOURCE = WILSON MIXED-LOG EXPANSION + CONNECTING TAIL
--
-- Compose R575 with R573/R574.
--
-- The preferred rational covariance extension has magnitude = |.| by
-- construction, so the historical magnitude-calibration field disappears.
--
-- Remaining Wilson-specific physical content:
--
--   W1  selected Wilson mixed-log response = connected cluster sum;
--   W3  absolute connecting-cluster weight sum <= rooted shell.
--
-- Bounded-test/time/order closure data remain ordinary downstream semantics,
-- not an additional localization theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.YangMillsRationalAbsoluteCovarianceExtensionRound575Exact as R575
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonMixedLogCovarianceRound573Exact as R573
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonWEXTCompletionRound574Exact as R574

record PreferredWilsonMixedLogPhysicalSource
    {Measure Observable : Set}
    (dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    (laws :
      R575.RationalCovarianceContinuityLaws dataSet)
    : Set₁ where
  field
    SourceDirection Cluster : Set

    sourceCalculus :
      ∀ cutoff →
      Cumulant.NormalizedLogSourceCalculus
        (R573.r278MomentAlgebra
          (R575.rationalAbsoluteCovarianceExtension laws)
          (Gram.measureSequence dataSet cutoff))

    insertionMeaning :
      ∀ cutoff →
      Cumulant.LiteralTwoSourceInsertionMeaning
        (sourceCalculus cutoff)
        SourceDirection

    contributingClusters :
      Nat → Observable → Observable → List Cluster

    clusterWeight :
      Nat → Observable → Observable → Cluster → ℚ

    literalWilsonMixedLogIsConnectedClusterSum :
      ∀ cutoff left right →
      Cumulant.literalMixedSecondLogDerivative
        (insertionMeaning cutoff)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) left)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) right)
      ≡
      TwoMark.sumℚ
        (TwoMark.map
          (clusterWeight cutoff left right)
          (contributingClusters cutoff left right))

open PreferredWilsonMixedLogPhysicalSource public

asR573 :
  ∀ {Measure Observable dataSet laws}
    (source :
      PreferredWilsonMixedLogPhysicalSource
        {Measure = Measure} {Observable = Observable}
        dataSet laws) →
  R573.SourceFirstWilsonMixedLogClusterData
    {Measure = Measure}
    {Observable = Observable}
    {SourceDirection = SourceDirection source}
    {Cluster = Cluster source}
    dataSet
    (R575.rationalAbsoluteCovarianceExtension laws)
asR573 {laws = laws} source = record
  { R573.SourceFirstWilsonMixedLogClusterData.sourceCalculus =
      sourceCalculus source
  ; R573.SourceFirstWilsonMixedLogClusterData.insertionMeaning =
      insertionMeaning source
  ; R573.SourceFirstWilsonMixedLogClusterData.contributingClusters =
      contributingClusters source
  ; R573.SourceFirstWilsonMixedLogClusterData.clusterWeight =
      clusterWeight source
  ; R573.SourceFirstWilsonMixedLogClusterData.literalWilsonMixedLogIsConnectedClusterSum =
      literalWilsonMixedLogIsConnectedClusterSum source
  ; R573.SourceFirstWilsonMixedLogClusterData.magnitudeIsRationalAbsolute =
      R575.magnitudeIsRationalAbsolute laws
  }

record PreferredWilsonWEXTSource
    {Measure Observable Scale Volume Root : Set}
    (dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    (laws :
      R575.RationalCovarianceContinuityLaws dataSet)
    : Set₂ where
  field
    mixedLog :
      PreferredWilsonMixedLogPhysicalSource dataSet laws

    shellData :
      Shell.TraversalShellData Scale Volume Root

    scaleOfCutoff : Nat → Scale
    volumeOfCutoff : Nat → Volume

    physicalDistance : Observable → Observable → Nat
    connectingRoot : Nat → Observable → Observable → Root

    ConnectingClusterMeetsBothSupports :
      Nat → Observable → Observable → Set

    absoluteConnectingWeightSumBelowRootedShell :
      ∀ cutoff left right →
      TwoMark.sumℚ
        (TwoMark.map
          (λ cluster →
            ∣ clusterWeight (mixedLog) cutoff left right cluster ∣)
          (contributingClusters (mixedLog) cutoff left right))
      ≤
      Shell.rootedShell shellData
        (scaleOfCutoff cutoff)
        (volumeOfCutoff cutoff)
        (connectingRoot cutoff left right)
        (physicalDistance left right)

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
      ∀ left right time →
      physicalDistance left (timeTranslate right time)
      ≡ time

    upperOrderClosed :
      ∀ sequence target upper →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper

open PreferredWilsonWEXTSource public

asR574 :
  ∀ {Measure Observable Scale Volume Root dataSet laws}
    (source :
      PreferredWilsonWEXTSource
        {Measure = Measure}
        {Observable = Observable}
        {Scale = Scale}
        {Volume = Volume}
        {Root = Root}
        dataSet laws) →
  R574.SourceFirstWilsonWEXTCompletion
    {Measure = Measure}
    {Observable = Observable}
    {SourceDirection = SourceDirection (mixedLog source)}
    {Cluster = Cluster (mixedLog source)}
    {Scale = Scale}
    {Volume = Volume}
    {Root = Root}
    dataSet
    (R575.rationalAbsoluteCovarianceExtension laws)
asR574 source = record
  { R574.SourceFirstWilsonWEXTCompletion.mixedLog =
      asR573 (mixedLog source)
  ; R574.SourceFirstWilsonWEXTCompletion.shellData =
      shellData source
  ; R574.SourceFirstWilsonWEXTCompletion.scaleOfCutoff =
      scaleOfCutoff source
  ; R574.SourceFirstWilsonWEXTCompletion.volumeOfCutoff =
      volumeOfCutoff source
  ; R574.SourceFirstWilsonWEXTCompletion.physicalDistance =
      physicalDistance source
  ; R574.SourceFirstWilsonWEXTCompletion.connectingRoot =
      connectingRoot source
  ; R574.SourceFirstWilsonWEXTCompletion.ConnectingClusterMeetsBothSupports =
      ConnectingClusterMeetsBothSupports source
  ; R574.SourceFirstWilsonWEXTCompletion.absoluteConnectingWeightSumBelowRootedShell =
      absoluteConnectingWeightSumBelowRootedShell source
  ; R574.SourceFirstWilsonWEXTCompletion.timeTranslate =
      timeTranslate source
  ; R574.SourceFirstWilsonWEXTCompletion.leftBounded =
      leftBounded source
  ; R574.SourceFirstWilsonWEXTCompletion.translatedRightBounded =
      translatedRightBounded source
  ; R574.SourceFirstWilsonWEXTCompletion.translatedProductBounded =
      translatedProductBounded source
  ; R574.SourceFirstWilsonWEXTCompletion.supportDistanceIsEuclideanTime =
      supportDistanceIsEuclideanTime source
  ; R574.SourceFirstWilsonWEXTCompletion.upperOrderClosed =
      upperOrderClosed source
  }

round576PreferredWEXTCompilerLevel : ProofLevel
round576PreferredWEXTCompilerLevel = machineChecked

round576MagnitudeCalibrationPhysicalInputRequired : Bool
round576MagnitudeCalibrationPhysicalInputRequired = false

literalRound576WilsonMixedLogClusterExpansionLevel : ProofLevel
literalRound576WilsonMixedLogClusterExpansionLevel =
  R573.literalRound573WilsonMixedLogClusterExpansionLevel

literalRound576ConnectingWeightTailLevel : ProofLevel
literalRound576ConnectingWeightTailLevel =
  R574.literalRound574ConnectingWeightTailLevel

round576RationalMagnitudeContinuityLevel : ProofLevel
round576RationalMagnitudeContinuityLevel =
  R575.round575RationalCovarianceContinuityLawsLevel
