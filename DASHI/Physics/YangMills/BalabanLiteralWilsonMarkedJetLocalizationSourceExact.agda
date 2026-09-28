{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralWilsonMarkedJetLocalizationSourceExact where

------------------------------------------------------------------------
-- PREFERRED LITERAL W1/W3 SOURCE AFTER JET REDUCTION
--
-- The target bivariate log jet is fixed by the exact normalized finite moments.
-- Therefore the source-native theorem has only two genuinely analytic pieces:
--
--   W1j  construct the marked polymer jets and prove their finite sum is the
--        normalized-moment log jet;
--
--   W3j  bound each two-support mixed jet coefficient by a shell charge and
--        sum those charges into the existing rooted shell.
--
-- Source-direction representation and arbitrary-function differentiation have
-- been eliminated.
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
import DASHI.Physics.YangMills.BalabanWilsonMarkedClusterJetExact as Jet
import DASHI.Physics.YangMills.BalabanLiteralWilsonWEXTTheoremExact as WEXT

record LiteralWilsonMarkedJetLocalizationSource
    {Measure Observable Cluster Scale Volume Root : Set}
    (dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    (laws :
      R575.RationalCovarianceContinuityLaws dataSet)
    : Set₂ where
  field
    sourceCalculus :
      ∀ cutoff →
      Cumulant.NormalizedLogSourceCalculus
        (R573.r278MomentAlgebra
          (R575.rationalAbsoluteCovarianceExtension laws)
          (Gram.measureSequence dataSet cutoff))

    markedJetExpansion :
      ∀ cutoff left right →
      Jet.NormalizedWilsonMarkedLogJetExpansion
        {Cluster = Cluster}
        (R573.r278MomentAlgebra
          (R575.rationalAbsoluteCovarianceExtension laws)
          (Gram.measureSequence dataSet cutoff))
        left right

    shellData :
      Shell.TraversalShellData Scale Volume Root

    scaleOfCutoff : Nat → Scale
    volumeOfCutoff : Nat → Volume
    physicalDistance : Observable → Observable → Nat
    connectingRoot : Nat → Observable → Observable → Root

    ConnectingClusterMeetsBothSupports :
      Nat → Observable → Observable → Set

    shellCharge :
      Nat → Observable → Observable → Cluster → ℚ

    pointwiseWilsonJetLocalization :
      ∀ cutoff left right cluster →
      ∣ Jet.mixed
          (Jet.clusterJet
            (markedJetExpansion cutoff left right)
            cluster) ∣
      ≤ shellCharge cutoff left right cluster

    localizedShellChargeSum :
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
        (physicalDistance left right)

open LiteralWilsonMarkedJetLocalizationSource public

record WilsonJetDownstreamSemantics
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

open WilsonJetDownstreamSemantics public

literalWilsonMarkedJetsCompileToR556 :
  ∀ {Measure Observable Cluster Scale Volume Root dataSet laws}
    (source :
      LiteralWilsonMarkedJetLocalizationSource
        {Measure = Measure}
        {Observable = Observable}
        {Cluster = Cluster}
        {Scale = Scale}
        {Volume = Volume}
        {Root = Root}
        dataSet laws)
    (semantics : WilsonJetDownstreamSemantics dataSet) →
  R556.IndexedSourceFirstWilsonCovarianceData
    {Measure = Measure}
    {Observable = Observable}
    {Scale = Scale}
    {Volume = Volume}
    {Root = Root}
    dataSet
    (R575.rationalAbsoluteCovarianceExtension laws)
literalWilsonMarkedJetsCompileToR556 source semantics =
  WEXT.literalWilsonCovarianceSourceFromNormalizedMarkedJets
    (sourceCalculus source)
    (markedJetExpansion source)
    (shellData source)
    (scaleOfCutoff source)
    (volumeOfCutoff source)
    (physicalDistance source)
    (connectingRoot source)
    (ConnectingClusterMeetsBothSupports source)
    (shellCharge source)
    (pointwiseWilsonJetLocalization source)
    (localizedShellChargeSum source)
    (timeTranslate semantics)
    (leftBounded semantics)
    (translatedRightBounded semantics)
    (translatedProductBounded semantics)
    (supportDistanceIsEuclideanTime semantics (physicalDistance source))
    (upperOrderClosed semantics)
