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

open import Agda.Builtin.Equality using (_≡_; cong)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.YangMillsRationalAbsoluteCovarianceExtensionRound575Exact as R575
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonMixedLogCovarianceRound573Exact as R573
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceRound556Exact as R556
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
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


------------------------------------------------------------------------
-- DIRECT preferred source: source calculus has disappeared entirely.
------------------------------------------------------------------------

record DirectLiteralWilsonMarkedJetLocalizationSource
    {Measure Observable Cluster Scale Volume Root : Set}
    (dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    (laws :
      R575.RationalCovarianceContinuityLaws dataSet)
    : Set₂ where
  field
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

open DirectLiteralWilsonMarkedJetLocalizationSource public

directJetFiniteCovarianceBelowRootedShell :
  ∀ {Measure Observable Cluster Scale Volume Root dataSet laws}
    (source :
      DirectLiteralWilsonMarkedJetLocalizationSource
        {Measure = Measure}
        {Observable = Observable}
        {Cluster = Cluster}
        {Scale = Scale}
        {Volume = Volume}
        {Root = Root}
        dataSet laws)
    cutoff left right →
  R278.connectedCovarianceMagnitude
    (R575.rationalAbsoluteCovarianceExtension laws)
    (Gram.measureSequence dataSet cutoff)
    left right
  ≤
  Shell.rootedShell
    (shellData source)
    (scaleOfCutoff source cutoff)
    (volumeOfCutoff source cutoff)
    (connectingRoot source cutoff left right)
    (physicalDistance source left right)
directJetFiniteCovarianceBelowRootedShell
    {dataSet = dataSet} {laws = laws}
    source cutoff left right =
  let
    extension =
      R575.rationalAbsoluteCovarianceExtension laws
    measure =
      Gram.measureSequence dataSet cutoff
    expansion =
      markedJetExpansion source cutoff left right
    locality =
      Jet.supportLocality expansion
    connecting =
      Jet.filterTwoSupport
        (Jet.touchesLeft locality)
        (Jet.touchesRight locality)
        (Jet.clusters expansion)
    weight =
      λ cluster → Jet.mixed (Jet.clusterJet expansion cluster)
    charge =
      shellCharge source cutoff left right

    signedExpansion :
      Cumulant.connectedCovariance
        (R573.r278MomentAlgebra extension measure)
        left right
      ≡
      TwoMark.sumℚ (TwoMark.map weight connecting)
    signedExpansion =
      Jet.normalizedConnectedCovarianceIsTwoSupportClusterSum
        left right expansion

    triangle :
      ∣ Cumulant.connectedCovariance
          (R573.r278MomentAlgebra extension measure)
          left right ∣
      ≤
      TwoMark.sumℚ
        (TwoMark.map (λ cluster → ∣ weight cluster ∣) connecting)
    triangle =
      subst
        (λ value →
          ∣ value ∣
          ≤
          TwoMark.sumℚ
            (TwoMark.map (λ cluster → ∣ weight cluster ∣) connecting))
        (sym signedExpansion)
        (Jet.absoluteSumBelowSumAbsolute connecting weight)

    charged :
      TwoMark.sumℚ
        (TwoMark.map (λ cluster → ∣ weight cluster ∣) connecting)
      ≤
      TwoMark.sumℚ
        (TwoMark.map charge connecting)
    charged =
      WEXT.sumMapPointwiseMonotone
        connecting
        (λ cluster → ∣ weight cluster ∣)
        charge
        (pointwiseWilsonJetLocalization source cutoff left right)

    genericAbsoluteBelow :
      ∣ Cumulant.connectedCovariance
          (R573.r278MomentAlgebra extension measure)
          left right ∣
      ≤
      Shell.rootedShell
        (shellData source)
        (scaleOfCutoff source cutoff)
        (volumeOfCutoff source cutoff)
        (connectingRoot source cutoff left right)
        (physicalDistance source left right)
    genericAbsoluteBelow =
      ℚP.≤-trans triangle
        (ℚP.≤-trans charged
          (localizedShellChargeSum source cutoff left right))

    genericIsR278 :
      Cumulant.connectedCovariance
        (R573.r278MomentAlgebra extension measure)
        left right
      ≡
      R278.connectedCovarianceValue extension measure left right
    genericIsR278 =
      R573.r278ConnectedCovarianceIsGenericCumulant
        extension measure left right
  in
  subst
    (λ lower →
      lower
      ≤
      Shell.rootedShell
        (shellData source)
        (scaleOfCutoff source cutoff)
        (volumeOfCutoff source cutoff)
        (connectingRoot source cutoff left right)
        (physicalDistance source left right))
    (cong ∣_∣ genericIsR278)
    genericAbsoluteBelow

directLiteralWilsonMarkedJetsCompileToR556 :
  ∀ {Measure Observable Cluster Scale Volume Root dataSet laws}
    (source :
      DirectLiteralWilsonMarkedJetLocalizationSource
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
directLiteralWilsonMarkedJetsCompileToR556 source semantics = record
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
      timeTranslate semantics
  ; R556.IndexedSourceFirstWilsonCovarianceData.finiteWilsonCovarianceBelowConnectingShell =
      directJetFiniteCovarianceBelowRootedShell source
  ; R556.IndexedSourceFirstWilsonCovarianceData.ConnectingClusterMeetsBothWilsonSupports =
      ConnectingClusterMeetsBothSupports source
  ; R556.IndexedSourceFirstWilsonCovarianceData.leftBounded =
      leftBounded semantics
  ; R556.IndexedSourceFirstWilsonCovarianceData.translatedRightBounded =
      translatedRightBounded semantics
  ; R556.IndexedSourceFirstWilsonCovarianceData.translatedProductBounded =
      translatedProductBounded semantics
  ; R556.IndexedSourceFirstWilsonCovarianceData.supportDistanceIsEuclideanTime =
      supportDistanceIsEuclideanTime semantics (physicalDistance source)
  ; R556.IndexedSourceFirstWilsonCovarianceData.upperOrderClosed =
      upperOrderClosed semantics
  }
