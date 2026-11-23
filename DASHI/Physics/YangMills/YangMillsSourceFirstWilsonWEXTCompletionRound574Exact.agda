{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSourceFirstWilsonWEXTCompletionRound574Exact where

------------------------------------------------------------------------
-- GOAL-1 B1 / ROUND574:
-- MIXED-LOG CLUSTER SOURCE + W3 TAIL -> EXACT R556 WILSON COVARIANCE SOURCE
--
-- Preferred B1 source object contains:
--
--   * R573 literal Wilson mixed-log cluster expansion on exact R278 moments;
--   * rooted-shell geometry;
--   * W3 absolute connecting-cluster weight tail;
--   * bounded-test / Euclidean-time / order-closure semantics.
--
-- The final
--
--   R278.connectedCovarianceMagnitude <= rootedShell
--
-- is theorem output, not a source field.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.BalabanWilsonWEXTFromMixedLogRound552Exact as R552
import DASHI.Physics.YangMills.BalabanWilsonWEXTMaxCutExact as R494
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonMixedLogCovarianceExact as R573
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceExact as R556

record SourceFirstWilsonWEXTCompletion
    {Measure Observable SourceDirection Cluster Scale Volume Root : Set}
    (dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    (extension :
      R278.ScalarCovarianceConvergenceExtension dataSet)
    : Set₁ where
  field
    mixedLog :
      R573.SourceFirstWilsonMixedLogClusterData
        {Measure = Measure}
        {Observable = Observable}
        {SourceDirection = SourceDirection}
        {Cluster = Cluster}
        dataSet extension

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
            ∣ R573.clusterWeight mixedLog cutoff left right cluster ∣)
          (R573.contributingClusters mixedLog cutoff left right))
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

open SourceFirstWilsonWEXTCompletion public

asR552 :
  ∀ {Measure Observable SourceDirection Cluster Scale Volume Root dataSet extension} →
  SourceFirstWilsonWEXTCompletion
    {Measure = Measure}
    {Observable = Observable}
    {SourceDirection = SourceDirection}
    {Cluster = Cluster}
    {Scale = Scale}
    {Volume = Volume}
    {Root = Root}
    dataSet extension →
  R552.WilsonWEXTFromMixedLogSource
    Scale Volume Root Nat Observable SourceDirection Cluster
asR552 source = record
  { R552.WilsonWEXTFromMixedLogSource.expansion =
      R573.asR551 (mixedLog source)
  ; R552.WilsonWEXTFromMixedLogSource.shellData =
      shellData source
  ; R552.WilsonWEXTFromMixedLogSource.stateAtScale =
      λ cutoff → cutoff
  ; R552.WilsonWEXTFromMixedLogSource.scaleOf =
      scaleOfCutoff source
  ; R552.WilsonWEXTFromMixedLogSource.volumeOf =
      volumeOfCutoff source
  ; R552.WilsonWEXTFromMixedLogSource.physicalDistance =
      physicalDistance source
  ; R552.WilsonWEXTFromMixedLogSource.connectingRoot =
      connectingRoot source
  ; R552.WilsonWEXTFromMixedLogSource.ConnectingClusterMeetsBothSupports =
      ConnectingClusterMeetsBothSupports source
  ; R552.WilsonWEXTFromMixedLogSource.absoluteConnectingWeightSumBelowRootedShell =
      absoluteConnectingWeightSumBelowRootedShell source
  }

finiteSelectedCovarianceBelowRootedShell :
  ∀ {Measure Observable SourceDirection Cluster Scale Volume Root dataSet extension}
    (source :
      SourceFirstWilsonWEXTCompletion
        {Measure = Measure}
        {Observable = Observable}
        {SourceDirection = SourceDirection}
        {Cluster = Cluster}
        {Scale = Scale}
        {Volume = Volume}
        {Root = Root}
        dataSet extension)
    cutoff left right →
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    left right
  ≤
  Shell.rootedShell (shellData source)
    (scaleOfCutoff source cutoff)
    (volumeOfCutoff source cutoff)
    (connectingRoot source cutoff left right)
    (physicalDistance source left right)
finiteSelectedCovarianceBelowRootedShell
    {extension = extension} source cutoff left right =
  let
    wext = R552.asR494 (asR552 source)

    absoluteBound :
      ∣ R494.connectedCovariance wext cutoff left right ∣
      ≤
      Shell.rootedShell (shellData source)
        (scaleOfCutoff source cutoff)
        (volumeOfCutoff source cutoff)
        (connectingRoot source cutoff left right)
        (physicalDistance source left right)
    absoluteBound =
      R494.wilsonConnectedCovarianceBelowRootedShell
        wext cutoff left right

    sameMagnitude :
      ∣ R494.connectedCovariance wext cutoff left right ∣
      ≡
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff)
        left right
    sameMagnitude =
      R573.genericAbsoluteCovarianceIsR278Magnitude
        (mixedLog source) cutoff left right
  in
  subst
    (λ lower →
      lower
      ≤
      Shell.rootedShell (shellData source)
        (scaleOfCutoff source cutoff)
        (volumeOfCutoff source cutoff)
        (connectingRoot source cutoff left right)
        (physicalDistance source left right))
    sameMagnitude
    absoluteBound

asR556 :
  ∀ {Measure Observable SourceDirection Cluster Scale Volume Root dataSet extension} →
  SourceFirstWilsonWEXTCompletion
    {Measure = Measure}
    {Observable = Observable}
    {SourceDirection = SourceDirection}
    {Cluster = Cluster}
    {Scale = Scale}
    {Volume = Volume}
    {Root = Root}
    dataSet extension →
  R556.IndexedSourceFirstWilsonCovarianceData
    {Measure = Measure}
    {Observable = Observable}
    {Scale = Scale}
    {Volume = Volume}
    {Root = Root}
    dataSet extension
asR556 source = record
  { R556.IndexedSourceFirstWilsonCovarianceData.shellData =
      shellData source
  ; R556.IndexedSourceFirstWilsonCovarianceData.scaleOfCutoff =
      scaleOfCutoff source
  ; R556.IndexedSourceFirstWilsonCovarianceData.volumeOfCutoff =
      volumeOfCutoff source
  ; R556.IndexedSourceFirstWilsonCovarianceData.physicalDistance =
      physicalDistance source
  ; R556.IndexedSourceFirstWilsonCovarianceData.connectingRoot =
      connectingRoot source
  ; R556.IndexedSourceFirstWilsonCovarianceData.timeTranslate =
      timeTranslate source
  ; R556.IndexedSourceFirstWilsonCovarianceData.finiteWilsonCovarianceBelowConnectingShell =
      finiteSelectedCovarianceBelowRootedShell source
  ; R556.IndexedSourceFirstWilsonCovarianceData.ConnectingClusterMeetsBothWilsonSupports =
      ConnectingClusterMeetsBothSupports source
  ; R556.IndexedSourceFirstWilsonCovarianceData.leftBounded =
      leftBounded source
  ; R556.IndexedSourceFirstWilsonCovarianceData.translatedRightBounded =
      translatedRightBounded source
  ; R556.IndexedSourceFirstWilsonCovarianceData.translatedProductBounded =
      translatedProductBounded source
  ; R556.IndexedSourceFirstWilsonCovarianceData.supportDistanceIsEuclideanTime =
      supportDistanceIsEuclideanTime source
  ; R556.IndexedSourceFirstWilsonCovarianceData.upperOrderClosed =
      upperOrderClosed source
  }

finalWilsonShellCompilerLevel : ProofLevel
finalWilsonShellCompilerLevel = machineChecked

sourceFirstCovarianceAdapterLevel : ProofLevel
sourceFirstCovarianceAdapterLevel = machineChecked

sourceFirstWilsonWEXTCompletionLevel : ProofLevel
sourceFirstWilsonWEXTCompletionLevel = conditional

finalShellBoundStoredAsPhysicalInput : Bool
finalShellBoundStoredAsPhysicalInput = false

wilsonMixedLogClusterExpansionLevel : ProofLevel
wilsonMixedLogClusterExpansionLevel =
  R573.wilsonMixedLogClusterExpansionLevel

wilsonConnectingWeightTailLevel : ProofLevel
wilsonConnectingWeightTailLevel =
  R552.wilsonConnectingWeightTailLevel

wilsonMagnitudeCalibrationLevel : ProofLevel
wilsonMagnitudeCalibrationLevel =
  R573.wilsonMagnitudeIsRationalAbsoluteLevel
