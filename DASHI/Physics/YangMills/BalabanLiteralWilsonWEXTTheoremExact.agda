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
open import Relation.Binary.PropositionalEquality using (trans)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.YangMillsRationalAbsoluteCovarianceExtensionRound575Exact as R575
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonMixedLogCovarianceRound573Exact as R573
import DASHI.Physics.YangMills.YangMillsPreferredWilsonWEXTSourceRound576Exact as R576
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonWEXTCompletionRound574Exact as R574
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceRound556Exact as R556
import DASHI.Physics.YangMills.BalabanWilsonMarkedClusterDifferentiationExact as Diff
import DASHI.Physics.YangMills.BalabanObservableIndexedT5SourceMeaningRound403Exact as R403
import DASHI.Physics.YangMills.BalabanWilsonMarkedClusterJetExact as Jet


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


literalWilsonMixedLogFromMarkedClusterExpansion :
  ∀ {Measure Observable SourceDirection Cluster Source}
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
    (derivativeCalculus :
      Nat → Observable → Observable →
      Diff.MixedSourceDerivativeCalculus Source)
    (markedExpansion :
      ∀ cutoff left right →
      Diff.SourceDependentClusterExpansion
        Source Cluster
        (derivativeCalculus cutoff left right))
    (literalResponseIsMarkedMixedDerivative :
      ∀ cutoff left right →
      Cumulant.literalMixedSecondLogDerivative
        (insertionMeaning cutoff)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) left)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) right)
      ≡
      Diff.mixedDerivative
        (derivativeCalculus cutoff left right)
        (Diff.logPartition (markedExpansion cutoff left right))) →
  R576.PreferredWilsonMixedLogPhysicalSource dataSet laws
literalWilsonMixedLogFromMarkedClusterExpansion
    sourceCalculus insertionMeaning derivativeCalculus markedExpansion
    literalResponseIsMarkedMixedDerivative =
  literalWilsonMixedLogTheorem
    sourceCalculus
    insertionMeaning
    (λ cutoff left right →
      Diff.contributingClusters (markedExpansion cutoff left right))
    (λ cutoff left right cluster →
      Diff.mixedDerivative
        (derivativeCalculus cutoff left right)
        (Diff.clusterTerm (markedExpansion cutoff left right) cluster))
    (λ cutoff left right →
      trans
        (literalResponseIsMarkedMixedDerivative cutoff left right)
        (Diff.mixedDerivativeIsConnectedClusterDerivativeSum
          (markedExpansion cutoff left right)))

literalWilsonMixedLogFromFullMarkedClusterExpansion :
  ∀ {Measure Observable SourceDirection Cluster Source}
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
    (derivativeCalculus :
      Nat → Observable → Observable →
      Diff.MixedSourceDerivativeCalculus Source)
    (derivativeVanishing :
      ∀ cutoff left right →
      Diff.MixedSourceDerivativeVanishing
        (derivativeCalculus cutoff left right))
    (markedExpansion :
      ∀ cutoff left right →
      Diff.FullMarkedClusterExpansion
        Source Cluster
        (derivativeCalculus cutoff left right))
    (literalResponseIsMarkedMixedDerivative :
      ∀ cutoff left right →
      Cumulant.literalMixedSecondLogDerivative
        (insertionMeaning cutoff)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) left)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) right)
      ≡
      Diff.mixedDerivative
        (derivativeCalculus cutoff left right)
        (Diff.logPartition (markedExpansion cutoff left right))) →
  R576.PreferredWilsonMixedLogPhysicalSource dataSet laws
literalWilsonMixedLogFromFullMarkedClusterExpansion
    sourceCalculus insertionMeaning derivativeCalculus derivativeVanishing
    markedExpansion literalResponseIsMarkedMixedDerivative =
  literalWilsonMixedLogTheorem
    sourceCalculus
    insertionMeaning
    (λ cutoff left right →
      Diff.connectingClusters (markedExpansion cutoff left right))
    (λ cutoff left right cluster →
      Diff.mixedDerivative
        (derivativeCalculus cutoff left right)
        (Diff.clusterTerm (markedExpansion cutoff left right) cluster))
    (λ cutoff left right →
      trans
        (literalResponseIsMarkedMixedDerivative cutoff left right)
        (Diff.mixedDerivativeFullExpansionIsConnectingSum
          (derivativeVanishing cutoff left right)
          (markedExpansion cutoff left right))))


literalWilsonMixedLogFromSupportIndexedMarkedExpansion :
  ∀ {Measure Observable SourceDirection Cluster Source}
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
    (derivativeCalculus :
      Nat → Observable → Observable →
      Diff.MixedSourceDerivativeCalculus Source)
    (derivativeVanishing :
      ∀ cutoff left right →
      Diff.MixedSourceDerivativeVanishing
        (derivativeCalculus cutoff left right))
    (markedExpansion :
      ∀ cutoff left right →
      Diff.SupportIndexedMarkedClusterExpansion
        Source Cluster
        (derivativeCalculus cutoff left right))
    (literalResponseIsMarkedMixedDerivative :
      ∀ cutoff left right →
      Cumulant.literalMixedSecondLogDerivative
        (insertionMeaning cutoff)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) left)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) right)
      ≡
      Diff.mixedDerivative
        (derivativeCalculus cutoff left right)
        (Diff.logPartition (markedExpansion cutoff left right))) →
  R576.PreferredWilsonMixedLogPhysicalSource dataSet laws
literalWilsonMixedLogFromSupportIndexedMarkedExpansion
    sourceCalculus insertionMeaning derivativeCalculus derivativeVanishing
    markedExpansion literalResponseIsMarkedMixedDerivative =
  literalWilsonMixedLogTheorem
    sourceCalculus
    insertionMeaning
    (λ cutoff left right →
      let expansion = markedExpansion cutoff left right
          locality = Diff.supportLocality expansion
      in
      Diff.filterTwoSupport
        (Diff.touchesLeft locality)
        (Diff.touchesRight locality)
        (Diff.clusters expansion))
    (λ cutoff left right cluster →
      Diff.mixedDerivative
        (derivativeCalculus cutoff left right)
        (Diff.clusterTerm (markedExpansion cutoff left right) cluster))
    (λ cutoff left right →
      trans
        (literalResponseIsMarkedMixedDerivative cutoff left right)
        (Diff.mixedDerivativeSupportIndexedExpansionIsConnectingSum
          (derivativeVanishing cutoff left right)
          (markedExpansion cutoff left right))))


------------------------------------------------------------------------
-- W3 finite summation payment.
--
-- The physical/localization input should be pointwise: each actual
-- Wilson-marked connected cluster is charged by a nonnegative shell charge.
-- Once the total shell charge is already bounded by the selected rooted shell,
-- finite summation is ordinary rational order algebra.
------------------------------------------------------------------------

sumMapPointwiseMonotone :
  ∀ {A : Set}
    (items : List A)
    (lower upper : A → ℚ) →
  (∀ item → lower item ≤ upper item) →
  TwoMark.sumℚ (TwoMark.map lower items)
  ≤ TwoMark.sumℚ (TwoMark.map upper items)
sumMapPointwiseMonotone [] lower upper pointwise =
  ℚP.≤-refl
sumMapPointwiseMonotone (item ∷ items) lower upper pointwise =
  ℚP.+-mono-≤
    (pointwise item)
    (sumMapPointwiseMonotone items lower upper pointwise)

absoluteConnectingWeightSumBelowRootedShellFromPointwiseLocalization :
  ∀ {Cluster Scale Volume Root}
    (clusters : List Cluster)
    (weight : Cluster → ℚ)
    (shellCharge : Cluster → ℚ)
    (shellData : Shell.TraversalShellData Scale Volume Root)
    (scale : Scale)
    (volume : Volume)
    (root : Root)
    (distance : Nat) →
  (∀ cluster → ∣ weight cluster ∣ ≤ shellCharge cluster) →
  TwoMark.sumℚ (TwoMark.map shellCharge clusters)
    ≤ Shell.rootedShell shellData scale volume root distance →
  TwoMark.sumℚ
    (TwoMark.map (λ cluster → ∣ weight cluster ∣) clusters)
    ≤ Shell.rootedShell shellData scale volume root distance
absoluteConnectingWeightSumBelowRootedShellFromPointwiseLocalization
    clusters weight shellCharge shellData scale volume root distance
    pointwise localizedShellSum =
  ℚP.≤-trans
    (sumMapPointwiseMonotone
      clusters
      (λ cluster → ∣ weight cluster ∣)
      shellCharge
      pointwise)
    localizedShellSum

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


------------------------------------------------------------------------
-- Preferred W3 constructor from LOCAL Wilson-cluster localization.
------------------------------------------------------------------------

literalPreferredWilsonWEXTFromPointwiseLocalization :
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
    (shellCharge :
      Nat → Observable → Observable →
      R576.Cluster mixedLog → ℚ)
    (pointwiseWilsonClusterLocalization :
      ∀ cutoff left right cluster →
      ∣ R576.clusterWeight mixedLog cutoff left right cluster ∣
      ≤ shellCharge cutoff left right cluster)
    (localizedShellChargeSum :
      ∀ cutoff left right →
      TwoMark.sumℚ
        (TwoMark.map
          (shellCharge cutoff left right)
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
literalPreferredWilsonWEXTFromPointwiseLocalization
    mixedLog shellData scaleOfCutoff volumeOfCutoff physicalDistance
    connectingRoot ConnectingClusterMeetsBothSupports
    shellCharge pointwiseWilsonClusterLocalization localizedShellChargeSum
    timeTranslate leftBounded translatedRightBounded
    translatedProductBounded supportDistanceIsEuclideanTime
    upperOrderClosed =
  literalPreferredWilsonWEXTTheorem
    mixedLog
    shellData
    scaleOfCutoff
    volumeOfCutoff
    physicalDistance
    connectingRoot
    ConnectingClusterMeetsBothSupports
    (λ cutoff left right →
      absoluteConnectingWeightSumBelowRootedShellFromPointwiseLocalization
        (R576.contributingClusters mixedLog cutoff left right)
        (R576.clusterWeight mixedLog cutoff left right)
        (shellCharge cutoff left right)
        shellData
        (scaleOfCutoff cutoff)
        (volumeOfCutoff cutoff)
        (connectingRoot cutoff left right)
        (physicalDistance left right)
        (pointwiseWilsonClusterLocalization cutoff left right)
        (localizedShellChargeSum cutoff left right))
    timeTranslate
    leftBounded
    translatedRightBounded
    translatedProductBounded
    supportDistanceIsEuclideanTime
    upperOrderClosed


------------------------------------------------------------------------
-- Terminal W1+W3 constructor from one source-native marked-localization
-- package.  No intermediate printed-J or generic extensionActivity equality is
-- exposed to callers.
------------------------------------------------------------------------

literalPreferredWilsonWEXTFromSupportIndexedMarkedLocalization :
  ∀ {Measure Observable SourceDirection Cluster Source Scale Volume Root}
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
    (derivativeCalculus :
      Nat → Observable → Observable →
      Diff.MixedSourceDerivativeCalculus Source)
    (derivativeVanishing :
      ∀ cutoff left right →
      Diff.MixedSourceDerivativeVanishing
        (derivativeCalculus cutoff left right))
    (markedExpansion :
      ∀ cutoff left right →
      Diff.SupportIndexedMarkedClusterExpansion
        Source Cluster
        (derivativeCalculus cutoff left right))
    (literalResponseIsMarkedMixedDerivative :
      ∀ cutoff left right →
      Cumulant.literalMixedSecondLogDerivative
        (insertionMeaning cutoff)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) left)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) right)
      ≡
      Diff.mixedDerivative
        (derivativeCalculus cutoff left right)
        (Diff.logPartition (markedExpansion cutoff left right)))
    (shellData : Shell.TraversalShellData Scale Volume Root)
    (scaleOfCutoff : Nat → Scale)
    (volumeOfCutoff : Nat → Volume)
    (physicalDistance : Observable → Observable → Nat)
    (connectingRoot : Nat → Observable → Observable → Root)
    (ConnectingClusterMeetsBothSupports :
      Nat → Observable → Observable → Set)
    (shellCharge :
      Nat → Observable → Observable → Cluster → ℚ)
    (pointwiseWilsonClusterLocalization :
      ∀ cutoff left right cluster →
      let expansion = markedExpansion cutoff left right in
      ∣ Diff.mixedDerivative
          (derivativeCalculus cutoff left right)
          (Diff.clusterTerm expansion cluster) ∣
      ≤ shellCharge cutoff left right cluster)
    (localizedShellChargeSum :
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
literalPreferredWilsonWEXTFromSupportIndexedMarkedLocalization
    sourceCalculus insertionMeaning derivativeCalculus derivativeVanishing
    markedExpansion literalResponseIsMarkedMixedDerivative
    shellData scaleOfCutoff volumeOfCutoff physicalDistance connectingRoot
    ConnectingClusterMeetsBothSupports shellCharge
    pointwiseWilsonClusterLocalization localizedShellChargeSum
    timeTranslate leftBounded translatedRightBounded
    translatedProductBounded supportDistanceIsEuclideanTime upperOrderClosed =
  let
    mixedLog =
      literalWilsonMixedLogFromSupportIndexedMarkedExpansion
        sourceCalculus
        insertionMeaning
        derivativeCalculus
        derivativeVanishing
        markedExpansion
        literalResponseIsMarkedMixedDerivative
  in
  literalPreferredWilsonWEXTFromPointwiseLocalization
    mixedLog
    shellData
    scaleOfCutoff
    volumeOfCutoff
    physicalDistance
    connectingRoot
    ConnectingClusterMeetsBothSupports
    shellCharge
    pointwiseWilsonClusterLocalization
    localizedShellChargeSum
    timeTranslate
    leftBounded
    translatedRightBounded
    translatedProductBounded
    supportDistanceIsEuclideanTime
    upperOrderClosed


literalWilsonCovarianceSourceFromSupportIndexedMarkedLocalization :
  ∀ {Measure Observable SourceDirection Cluster Source Scale Volume Root}
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
    (derivativeCalculus :
      Nat → Observable → Observable →
      Diff.MixedSourceDerivativeCalculus Source)
    (derivativeVanishing :
      ∀ cutoff left right →
      Diff.MixedSourceDerivativeVanishing
        (derivativeCalculus cutoff left right))
    (markedExpansion :
      ∀ cutoff left right →
      Diff.SupportIndexedMarkedClusterExpansion
        Source Cluster
        (derivativeCalculus cutoff left right))
    (literalResponseIsMarkedMixedDerivative :
      ∀ cutoff left right →
      Cumulant.literalMixedSecondLogDerivative
        (insertionMeaning cutoff)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) left)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) right)
      ≡
      Diff.mixedDerivative
        (derivativeCalculus cutoff left right)
        (Diff.logPartition (markedExpansion cutoff left right)))
    (shellData : Shell.TraversalShellData Scale Volume Root)
    (scaleOfCutoff : Nat → Scale)
    (volumeOfCutoff : Nat → Volume)
    (physicalDistance : Observable → Observable → Nat)
    (connectingRoot : Nat → Observable → Observable → Root)
    (ConnectingClusterMeetsBothSupports :
      Nat → Observable → Observable → Set)
    (shellCharge :
      Nat → Observable → Observable → Cluster → ℚ)
    (pointwiseWilsonClusterLocalization :
      ∀ cutoff left right cluster →
      let expansion = markedExpansion cutoff left right in
      ∣ Diff.mixedDerivative
          (derivativeCalculus cutoff left right)
          (Diff.clusterTerm expansion cluster) ∣
      ≤ shellCharge cutoff left right cluster)
    (localizedShellChargeSum :
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
  R556.IndexedSourceFirstWilsonCovarianceData
    {Measure = Measure}
    {Observable = Observable}
    {Scale = Scale}
    {Volume = Volume}
    {Root = Root}
    dataSet
    (R575.rationalAbsoluteCovarianceExtension laws)
literalWilsonCovarianceSourceFromSupportIndexedMarkedLocalization
    sourceCalculus insertionMeaning derivativeCalculus derivativeVanishing
    markedExpansion literalResponseIsMarkedMixedDerivative
    shellData scaleOfCutoff volumeOfCutoff physicalDistance connectingRoot
    ConnectingClusterMeetsBothSupports shellCharge
    pointwiseWilsonClusterLocalization localizedShellChargeSum
    timeTranslate leftBounded translatedRightBounded
    translatedProductBounded supportDistanceIsEuclideanTime upperOrderClosed =
  R574.asR556
    (R576.asR574
      (literalPreferredWilsonWEXTFromSupportIndexedMarkedLocalization
        sourceCalculus
        insertionMeaning
        derivativeCalculus
        derivativeVanishing
        markedExpansion
        literalResponseIsMarkedMixedDerivative
        shellData
        scaleOfCutoff
        volumeOfCutoff
        physicalDistance
        connectingRoot
        ConnectingClusterMeetsBothSupports
        shellCharge
        pointwiseWilsonClusterLocalization
        localizedShellChargeSum
        timeTranslate
        leftBounded
        translatedRightBounded
        translatedProductBounded
        supportDistanceIsEuclideanTime
        upperOrderClosed))


------------------------------------------------------------------------
-- Preferred observable-indexed source specialization.
--
-- R403 removes SourceDirection representation debt: the literal source
-- direction is the physical Observable itself and the insertion semantics are
-- definitional.  The only W1 same-object payment retained below is therefore
-- the analytic equality between the normalized mixed source response and the
-- mixed derivative of the source-dependent marked cluster expansion.
------------------------------------------------------------------------

literalWilsonCovarianceSourceFromObservableIndexedMarkedLocalization :
  ∀ {Measure Observable Cluster Source Scale Volume Root}
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
    (derivativeCalculus :
      Nat → Observable → Observable →
      Diff.MixedSourceDerivativeCalculus Source)
    (derivativeVanishing :
      ∀ cutoff left right →
      Diff.MixedSourceDerivativeVanishing
        (derivativeCalculus cutoff left right))
    (markedExpansion :
      ∀ cutoff left right →
      Diff.SupportIndexedMarkedClusterExpansion
        Source Cluster
        (derivativeCalculus cutoff left right))
    (normalizedWilsonResponseIsMarkedMixedDerivative :
      ∀ cutoff left right →
      Cumulant.mixedSecondLogDerivative
        (sourceCalculus cutoff)
        left right
      ≡
      Diff.mixedDerivative
        (derivativeCalculus cutoff left right)
        (Diff.logPartition (markedExpansion cutoff left right)))
    (shellData : Shell.TraversalShellData Scale Volume Root)
    (scaleOfCutoff : Nat → Scale)
    (volumeOfCutoff : Nat → Volume)
    (physicalDistance : Observable → Observable → Nat)
    (connectingRoot : Nat → Observable → Observable → Root)
    (ConnectingClusterMeetsBothSupports :
      Nat → Observable → Observable → Set)
    (shellCharge :
      Nat → Observable → Observable → Cluster → ℚ)
    (pointwiseWilsonClusterLocalization :
      ∀ cutoff left right cluster →
      let expansion = markedExpansion cutoff left right in
      ∣ Diff.mixedDerivative
          (derivativeCalculus cutoff left right)
          (Diff.clusterTerm expansion cluster) ∣
      ≤ shellCharge cutoff left right cluster)
    (localizedShellChargeSum :
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
  R556.IndexedSourceFirstWilsonCovarianceData
    {Measure = Measure}
    {Observable = Observable}
    {Scale = Scale}
    {Volume = Volume}
    {Root = Root}
    dataSet
    (R575.rationalAbsoluteCovarianceExtension laws)
literalWilsonCovarianceSourceFromObservableIndexedMarkedLocalization
    sourceCalculus derivativeCalculus derivativeVanishing
    markedExpansion normalizedWilsonResponseIsMarkedMixedDerivative
    shellData scaleOfCutoff volumeOfCutoff physicalDistance connectingRoot
    ConnectingClusterMeetsBothSupports shellCharge
    pointwiseWilsonClusterLocalization localizedShellChargeSum
    timeTranslate leftBounded translatedRightBounded translatedProductBounded
    supportDistanceIsEuclideanTime upperOrderClosed =
  literalWilsonCovarianceSourceFromSupportIndexedMarkedLocalization
    sourceCalculus
    (λ cutoff → R403.canonicalObservableIndexedMeaning (sourceCalculus cutoff))
    derivativeCalculus
    derivativeVanishing
    markedExpansion
    normalizedWilsonResponseIsMarkedMixedDerivative
    shellData
    scaleOfCutoff
    volumeOfCutoff
    physicalDistance
    connectingRoot
    ConnectingClusterMeetsBothSupports
    shellCharge
    pointwiseWilsonClusterLocalization
    localizedShellChargeSum
    timeTranslate
    leftBounded
    translatedRightBounded
    translatedProductBounded
    supportDistanceIsEuclideanTime
    upperOrderClosed


------------------------------------------------------------------------
-- Jet-native W1.  This is the preferred exact source interface when the
-- analytic construction exposes Taylor coefficients rather than an abstract
-- derivative operator on arbitrary cluster functions.
------------------------------------------------------------------------

literalWilsonMixedLogFromMarkedJetExpansion :
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
    (markedJetExpansion :
      ∀ cutoff left right →
      Jet.WilsonMarkedLogJetExpansion Cluster)
    (literalResponseIsJetMixed :
      ∀ cutoff left right →
      Cumulant.literalMixedSecondLogDerivative
        (insertionMeaning cutoff)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) left)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) right)
      ≡
      Jet.mixed
        (Jet.literalLogPartitionJet
          (markedJetExpansion cutoff left right))) →
  R576.PreferredWilsonMixedLogPhysicalSource dataSet laws
literalWilsonMixedLogFromMarkedJetExpansion
    sourceCalculus insertionMeaning markedJetExpansion
    literalResponseIsJetMixed =
  literalWilsonMixedLogTheorem
    sourceCalculus
    insertionMeaning
    (λ cutoff left right →
      let expansion = markedJetExpansion cutoff left right
          locality = Jet.supportLocality expansion
      in
      Jet.filterTwoSupport
        (Jet.touchesLeft locality)
        (Jet.touchesRight locality)
        (Jet.clusters expansion))
    (λ cutoff left right cluster →
      Jet.mixed
        (Jet.clusterJet
          (markedJetExpansion cutoff left right)
          cluster))
    (λ cutoff left right →
      trans
        (literalResponseIsJetMixed cutoff left right)
        (Jet.mixedLogJetIsTwoSupportClusterSum
          (markedJetExpansion cutoff left right)))

literalWilsonCovarianceSourceFromObservableIndexedMarkedJets :
  ∀ {Measure Observable Cluster Scale Volume Root}
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
    (markedJetExpansion :
      ∀ cutoff left right →
      Jet.WilsonMarkedLogJetExpansion Cluster)
    (normalizedWilsonResponseIsJetMixed :
      ∀ cutoff left right →
      Cumulant.mixedSecondLogDerivative
        (sourceCalculus cutoff)
        left right
      ≡
      Jet.mixed
        (Jet.literalLogPartitionJet
          (markedJetExpansion cutoff left right)))
    (shellData : Shell.TraversalShellData Scale Volume Root)
    (scaleOfCutoff : Nat → Scale)
    (volumeOfCutoff : Nat → Volume)
    (physicalDistance : Observable → Observable → Nat)
    (connectingRoot : Nat → Observable → Observable → Root)
    (ConnectingClusterMeetsBothSupports :
      Nat → Observable → Observable → Set)
    (shellCharge :
      Nat → Observable → Observable → Cluster → ℚ)
    (pointwiseWilsonJetLocalization :
      ∀ cutoff left right cluster →
      ∣ Jet.mixed
          (Jet.clusterJet
            (markedJetExpansion cutoff left right)
            cluster) ∣
      ≤ shellCharge cutoff left right cluster)
    (localizedShellChargeSum :
      ∀ cutoff left right →
      let expansion = markedJetExpansion cutoff left right
          locality = Jet.supportLocality expansion
      in
      TwoMark.sumℚ
        (TwoMark.map
          (shellCharge cutoff left right)
          (Jet.filterTwoSupport
            (Jet.touchesLeft locality)
            (Jet.touchesRight locality)
            (Jet.clusters expansion)))
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
  R556.IndexedSourceFirstWilsonCovarianceData
    {Measure = Measure}
    {Observable = Observable}
    {Scale = Scale}
    {Volume = Volume}
    {Root = Root}
    dataSet
    (R575.rationalAbsoluteCovarianceExtension laws)
literalWilsonCovarianceSourceFromObservableIndexedMarkedJets
    sourceCalculus markedJetExpansion normalizedWilsonResponseIsJetMixed
    shellData scaleOfCutoff volumeOfCutoff physicalDistance connectingRoot
    ConnectingClusterMeetsBothSupports shellCharge
    pointwiseWilsonJetLocalization localizedShellChargeSum
    timeTranslate leftBounded translatedRightBounded translatedProductBounded
    supportDistanceIsEuclideanTime upperOrderClosed =
  let
    insertionMeaning =
      λ cutoff → R403.canonicalObservableIndexedMeaning (sourceCalculus cutoff)

    mixedLog =
      literalWilsonMixedLogFromMarkedJetExpansion
        sourceCalculus
        insertionMeaning
        markedJetExpansion
        normalizedWilsonResponseIsJetMixed

    preferred =
      literalPreferredWilsonWEXTFromPointwiseLocalization
        mixedLog
        shellData
        scaleOfCutoff
        volumeOfCutoff
        physicalDistance
        connectingRoot
        ConnectingClusterMeetsBothSupports
        shellCharge
        pointwiseWilsonJetLocalization
        localizedShellChargeSum
        timeTranslate
        leftBounded
        translatedRightBounded
        translatedProductBounded
        supportDistanceIsEuclideanTime
        upperOrderClosed
  in
  R574.asR556 (R576.asR574 preferred)


------------------------------------------------------------------------
-- Preferred normalized-moment jet route.
--
-- The expansion target is fixed by the exact finite expectation algebra, so no
-- separate mixed-response equality is a physical input.
------------------------------------------------------------------------

literalWilsonMixedLogFromNormalizedMarkedJetExpansion :
  ∀ {Measure Observable Cluster}
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
    (markedJetExpansion :
      ∀ cutoff left right →
      Jet.NormalizedWilsonMarkedLogJetExpansion
        {Cluster = Cluster}
        (R573.r278MomentAlgebra
          (R575.rationalAbsoluteCovarianceExtension laws)
          (Gram.measureSequence dataSet cutoff))
        left right) →
  R576.PreferredWilsonMixedLogPhysicalSource dataSet laws
literalWilsonMixedLogFromNormalizedMarkedJetExpansion
    sourceCalculus markedJetExpansion =
  literalWilsonMixedLogTheorem
    sourceCalculus
    (λ cutoff → R403.canonicalObservableIndexedMeaning (sourceCalculus cutoff))
    (λ cutoff left right →
      let expansion = markedJetExpansion cutoff left right
          locality = Jet.supportLocality expansion
      in
      Jet.filterTwoSupport
        (Jet.touchesLeft locality)
        (Jet.touchesRight locality)
        (Jet.clusters expansion))
    (λ cutoff left right cluster →
      Jet.mixed
        (Jet.clusterJet
          (markedJetExpansion cutoff left right)
          cluster))
    (λ cutoff left right →
      Jet.normalizedMixedLogIsTwoSupportClusterSum
        (sourceCalculus cutoff)
        left
        right
        (markedJetExpansion cutoff left right))

literalWilsonCovarianceSourceFromNormalizedMarkedJets :
  ∀ {Measure Observable Cluster Scale Volume Root}
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
    (markedJetExpansion :
      ∀ cutoff left right →
      Jet.NormalizedWilsonMarkedLogJetExpansion
        {Cluster = Cluster}
        (R573.r278MomentAlgebra
          (R575.rationalAbsoluteCovarianceExtension laws)
          (Gram.measureSequence dataSet cutoff))
        left right)
    (shellData : Shell.TraversalShellData Scale Volume Root)
    (scaleOfCutoff : Nat → Scale)
    (volumeOfCutoff : Nat → Volume)
    (physicalDistance : Observable → Observable → Nat)
    (connectingRoot : Nat → Observable → Observable → Root)
    (ConnectingClusterMeetsBothSupports :
      Nat → Observable → Observable → Set)
    (shellCharge :
      Nat → Observable → Observable → Cluster → ℚ)
    (pointwiseWilsonJetLocalization :
      ∀ cutoff left right cluster →
      ∣ Jet.mixed
          (Jet.clusterJet
            (markedJetExpansion cutoff left right)
            cluster) ∣
      ≤ shellCharge cutoff left right cluster)
    (localizedShellChargeSum :
      ∀ cutoff left right →
      let expansion = markedJetExpansion cutoff left right
          locality = Jet.supportLocality expansion
      in
      TwoMark.sumℚ
        (TwoMark.map
          (shellCharge cutoff left right)
          (Jet.filterTwoSupport
            (Jet.touchesLeft locality)
            (Jet.touchesRight locality)
            (Jet.clusters expansion)))
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
  R556.IndexedSourceFirstWilsonCovarianceData
    {Measure = Measure}
    {Observable = Observable}
    {Scale = Scale}
    {Volume = Volume}
    {Root = Root}
    dataSet
    (R575.rationalAbsoluteCovarianceExtension laws)
literalWilsonCovarianceSourceFromNormalizedMarkedJets
    sourceCalculus markedJetExpansion
    shellData scaleOfCutoff volumeOfCutoff physicalDistance connectingRoot
    ConnectingClusterMeetsBothSupports shellCharge
    pointwiseWilsonJetLocalization localizedShellChargeSum
    timeTranslate leftBounded translatedRightBounded translatedProductBounded
    supportDistanceIsEuclideanTime upperOrderClosed =
  let
    mixedLog =
      literalWilsonMixedLogFromNormalizedMarkedJetExpansion
        sourceCalculus markedJetExpansion

    preferred =
      literalPreferredWilsonWEXTFromPointwiseLocalization
        mixedLog
        shellData
        scaleOfCutoff
        volumeOfCutoff
        physicalDistance
        connectingRoot
        ConnectingClusterMeetsBothSupports
        shellCharge
        pointwiseWilsonJetLocalization
        localizedShellChargeSum
        timeTranslate
        leftBounded
        translatedRightBounded
        translatedProductBounded
        supportDistanceIsEuclideanTime
        upperOrderClosed
  in
  R574.asR556 (R576.asR574 preferred)
