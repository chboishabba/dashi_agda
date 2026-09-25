{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralWilsonWEXTTheoremExact where

------------------------------------------------------------------------
-- B1 theorem-bearing constructors.
--
-- W1 is the exact mixed-log connected-cluster identity on the literal Wilson
-- insertion calculus.  W3 is the absolute connecting-cluster rooted-shell
-- estimate.  This module introduces neither a printed-J surrogate nor a second
-- summability theorem; it terminates in R576.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣; _≤_)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.YangMillsRationalAbsoluteCovarianceExtensionRound575Exact as R575
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonMixedLogCovarianceRound573Exact as R573
import DASHI.Physics.YangMills.YangMillsPreferredWilsonWEXTSourceRound576Exact as R576

literalWilsonMixedLogTheorem :
  ∀ {Measure Observable SourceDirection Cluster}
    {dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
    {laws :
      R575.RationalCovarianceContinuityLaws dataSet}
    (sourceCalculus :
      ∀ cutoff →
      Cumulant.NormalizedLogSourceCalculus
        (R573.r278MomentAlgebra
          (R575.rationalAbsoluteCovarianceExtension laws)
          (Gram.measureSequence dataSet cutoff)))
    (insertionMeaning :
      ∀ cutoff →
      Cumulant.LiteralTwoSourceInsertionMeaning
        (sourceCalculus cutoff)
        SourceDirection)
    (contributingClusters :
      Nat → Observable → Observable → List Cluster)
    (clusterWeight :
      Nat → Observable → Observable → Cluster → ℚ)
    (literalWilsonMixedLogIsConnectedClusterSum :
      ∀ cutoff left right →
      Cumulant.literalMixedSecondLogDerivative
        (insertionMeaning cutoff)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) left)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) right)
      ≡
      TwoMark.sumℚ
        (TwoMark.map
          (clusterWeight cutoff left right)
          (contributingClusters cutoff left right))) →
  R576.PreferredWilsonMixedLogPhysicalSource dataSet laws
literalWilsonMixedLogTheorem
    sourceCalculus insertionMeaning contributingClusters clusterWeight
    literalWilsonMixedLogIsConnectedClusterSum = record
  { R576.PreferredWilsonMixedLogPhysicalSource.SourceDirection =
      SourceDirection
  ; R576.PreferredWilsonMixedLogPhysicalSource.Cluster =
      Cluster
  ; R576.PreferredWilsonMixedLogPhysicalSource.sourceCalculus =
      sourceCalculus
  ; R576.PreferredWilsonMixedLogPhysicalSource.insertionMeaning =
      insertionMeaning
  ; R576.PreferredWilsonMixedLogPhysicalSource.contributingClusters =
      contributingClusters
  ; R576.PreferredWilsonMixedLogPhysicalSource.clusterWeight =
      clusterWeight
  ; R576.PreferredWilsonMixedLogPhysicalSource.literalWilsonMixedLogIsConnectedClusterSum =
      literalWilsonMixedLogIsConnectedClusterSum
  }

literalPreferredWilsonWEXTTheorem :
  ∀ {Measure Observable Scale Volume Root}
    {dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
    {laws :
      R575.RationalCovarianceContinuityLaws dataSet}
    (mixedLog :
      R576.PreferredWilsonMixedLogPhysicalSource dataSet laws)
    (shellData : Shell.TraversalShellData Scale Volume Root)
    (scaleOfCutoff : Nat → Scale)
    (volumeOfCutoff : Nat → Volume)
    (physicalDistance : Observable → Observable → Nat)
    (connectingRoot : Nat → Observable → Observable → Root)
    (ConnectingClusterMeetsBothSupports :
      Nat → Observable → Observable → Set)
    (absoluteConnectingWeightSumBelowRootedShell :
      ∀ cutoff left right →
      TwoMark.sumℚ
        (TwoMark.map
          (λ cluster →
            ∣ R576.clusterWeight mixedLog cutoff left right cluster ∣)
          (R576.contributingClusters mixedLog cutoff left right))
      ≤
      Shell.rootedShell shellData
        (scaleOfCutoff cutoff)
        (volumeOfCutoff cutoff)
        (connectingRoot cutoff left right)
        (physicalDistance left right))
    (timeTranslate : Observable → Nat → Observable)
    (leftBounded :
      ∀ observable →
      Gram.BoundedObservable dataSet observable)
    (translatedRightBounded :
      ∀ observable time →
      Gram.BoundedObservable dataSet (timeTranslate observable time))
    (translatedProductBounded :
      ∀ left right time →
      Gram.BoundedObservable dataSet
        (Gram.multiplyObservable (Gram.operations dataSet)
          left (timeTranslate right time)))
    (supportDistanceIsEuclideanTime :
      ∀ left right time →
      physicalDistance left (timeTranslate right time) ≡ time)
    (upperOrderClosed :
      ∀ sequence target upper →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper) →
  R576.PreferredWilsonWEXTSource
    {Measure = Measure}
    {Observable = Observable}
    {Scale = Scale}
    {Volume = Volume}
    {Root = Root}
    dataSet laws
literalPreferredWilsonWEXTTheorem
    mixedLog shellData scaleOfCutoff volumeOfCutoff physicalDistance
    connectingRoot ConnectingClusterMeetsBothSupports
    absoluteConnectingWeightSumBelowRootedShell
    timeTranslate leftBounded translatedRightBounded
    translatedProductBounded supportDistanceIsEuclideanTime
    upperOrderClosed = record
  { R576.PreferredWilsonWEXTSource.mixedLog = mixedLog
  ; R576.PreferredWilsonWEXTSource.shellData = shellData
  ; R576.PreferredWilsonWEXTSource.scaleOfCutoff = scaleOfCutoff
  ; R576.PreferredWilsonWEXTSource.volumeOfCutoff = volumeOfCutoff
  ; R576.PreferredWilsonWEXTSource.physicalDistance = physicalDistance
  ; R576.PreferredWilsonWEXTSource.connectingRoot = connectingRoot
  ; R576.PreferredWilsonWEXTSource.ConnectingClusterMeetsBothSupports =
      ConnectingClusterMeetsBothSupports
  ; R576.PreferredWilsonWEXTSource.absoluteConnectingWeightSumBelowRootedShell =
      absoluteConnectingWeightSumBelowRootedShell
  ; R576.PreferredWilsonWEXTSource.timeTranslate = timeTranslate
  ; R576.PreferredWilsonWEXTSource.leftBounded = leftBounded
  ; R576.PreferredWilsonWEXTSource.translatedRightBounded =
      translatedRightBounded
  ; R576.PreferredWilsonWEXTSource.translatedProductBounded =
      translatedProductBounded
  ; R576.PreferredWilsonWEXTSource.supportDistanceIsEuclideanTime =
      supportDistanceIsEuclideanTime
  ; R576.PreferredWilsonWEXTSource.upperOrderClosed = upperOrderClosed
  }
