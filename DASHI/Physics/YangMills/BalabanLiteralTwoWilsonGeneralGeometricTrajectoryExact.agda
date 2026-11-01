{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonGeneralGeometricTrajectoryExact where

------------------------------------------------------------------------
-- Literal two-Wilson CMP116 theorem -> GENERAL Aq^d finite trajectory.
--
-- The mass-gap consumer does not require the historical normalization
--
--   A = 1/4, q = 1/2.
--
-- R273 accepts any cutoff-uniform rational amplitude/ratio with
--
--   A >= 0, 0 <= q < 1,
--
-- and a finite connected-covariance bound A q^distance.
--
-- This module therefore keeps the R444/R445 source theorem on its native real
-- carrier, asks only that its source amplitude and residual weight are bounded
-- by the image of ONE rational A,q pair, reflects the resulting order back to
-- ℚ, and constructs the route-neutral QuantitativeCorrelationDecayTrajectory.
--
-- This removes the artificial sourceAmplitude<=1/4 and residual<=2^-d
-- obligations from the preferred H1 route.  The quarter/half completion remains
-- a stronger optional specialization.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base as Nat using (_≤_; z≤n; s≤s)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_; ≤ℝ-refl; ≤ℝ-trans; mulMonotoneNonnegative)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanCMP116R429MixedLogResponseRound445Exact as R445
import DASHI.Physics.YangMills.BalabanCMP116CanonicalDomainRateSplitRound448Exact as R448
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPhysicalDecayRound451Exact as R451
import DASHI.Physics.YangMills.BalabanCMP116ConnectedCorePathRound453Exact as R453
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPhysicalSeparationRound450Exact as R450
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonMarkedExpansionTheoremExact as Literal
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Base
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Add
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Ring
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanExponentialToDyadicShellCoarseningExact as Coarsen
import DASHI.Physics.YangMills.BalabanSourceNativeGeometricMajorantRound395Exact as Native
import DASHI.Physics.YangMills.BalabanSourceNativeDistanceLowerRound388Exact as R388
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified
import DASHI.Physics.YangMills.YMSupportGraphDistance as Graph

orderedEmbedding :
  Ring.RationalRealRingEmbedding →
  Base.OrderedRationalRealEmbedding
orderedEmbedding embedding =
  Add.base (Ring.additive embedding)

embedQ :
  Ring.RationalRealRingEmbedding →
  ℚ → ℝ
embedQ embedding =
  Base.embed (orderedEmbedding embedding)

rationalPowerNonnegative :
  ∀ ratio →
  0ℚ ≤ ratio →
  ∀ depth →
  0ℚ ≤ Power.rationalPower ratio depth
rationalPowerNonnegative ratio ratioNN depth =
  subst
    (λ power → 0ℚ ≤ power)
    (Native.dyadicPowerIsPower ratio depth)
    (Coarsen.powerNonnegative ratio ratioNN depth)


rationalPowerAtMostOne :
  ∀ ratio →
  0ℚ ≤ ratio →
  ratio ≤ 1ℚ →
  ∀ depth →
  Power.rationalPower ratio depth ≤ 1ℚ
rationalPowerAtMostOne ratio ratioNN ratio≤1 zero =
  ℚP.≤-refl
rationalPowerAtMostOne ratio ratioNN ratio≤1 (suc depth) =
  let
    productBelowOne :
      Power.rationalPower ratio depth * ratio ≤ 1ℚ * 1ℚ
    productBelowOne =
      ℚP.*-mono-≤
        (rationalPowerNonnegative ratio ratioNN depth)
        (rationalPowerAtMostOne ratio ratioNN ratio≤1 depth)
        ratioNN
        ratio≤1
  in
  subst
    (λ upper →
      Power.rationalPower ratio (suc depth) ≤ upper)
    (ℚP.*-identityˡ 1ℚ)
    productBelowOne

rationalPowerAntitone :
  ∀ ratio →
  0ℚ ≤ ratio →
  ratio ≤ 1ℚ →
  ∀ {near far : Nat} →
  near Nat.≤ far →
  Power.rationalPower ratio far ≤ Power.rationalPower ratio near
rationalPowerAntitone ratio ratioNN ratio≤1
    {zero} {far} z≤n =
  rationalPowerAtMostOne ratio ratioNN ratio≤1 far
rationalPowerAntitone ratio ratioNN ratio≤1
    {suc near} {suc far} (s≤s proof) =
  ℚP.*-mono-≤
    (rationalPowerNonnegative ratio ratioNN far)
    (rationalPowerAntitone ratio ratioNN ratio≤1 proof)
    ratioNN
    ℚP.≤-refl

rationalPowerDistanceAntitoneFromStrictUnit :
  ∀ ratio →
  0ℚ ≤ ratio →
  ratio < 1ℚ →
  R388.RationalPowerDistanceAntitone ratio
rationalPowerDistanceAntitoneFromStrictUnit ratio ratioNN ratio<1 = record
  { R388.RationalPowerDistanceAntitone.ratioNonnegative = ratioNN
  ; R388.RationalPowerDistanceAntitone.powerAntitone =
      rationalPowerAntitone ratio ratioNN (ℚP.<⇒≤ ratio<1)
  }

embeddedPowerNonnegative :
  (embedding : Ring.RationalRealRingEmbedding) →
  ∀ ratio →
  0ℚ ≤ ratio →
  ∀ depth →
  0ℝ ≤ℝ embedQ embedding (Power.rationalPower ratio depth)
embeddedPowerNonnegative embedding ratio ratioNN depth =
  subst
    (λ lower →
      lower ≤ℝ embedQ embedding (Power.rationalPower ratio depth))
    (Base.zeroExact (orderedEmbedding embedding))
    (Base.orderPreserving
      (orderedEmbedding embedding)
      (rationalPowerNonnegative ratio ratioNN depth))

embeddedGeometricProductExact :
  (embedding : Ring.RationalRealRingEmbedding) →
  ∀ amplitude ratio depth →
  embedQ embedding
    (amplitude * Power.rationalPower ratio depth)
  ≡
  embedQ embedding amplitude
    *ℝ embedQ embedding (Power.rationalPower ratio depth)
embeddedGeometricProductExact embedding amplitude ratio depth =
  Ring.multiplyExact embedding
    amplitude
    (Power.rationalPower ratio depth)

record GeneralGeometricTwoWilsonSource
    {Measure Observable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure}
        {TestObservable = Observable}
        {dataSet = dataSet}
        {extension = extension}
        base)
    (ringEmbedding : Ring.RationalRealRingEmbedding)
    (amplitude ratio : ℚ)
    : Set₁ where
  field
    mixedLog :
      R445.R429LiteralMixedLogResponse
        (R444.asR429 data)
        (orderedEmbedding ringEmbedding)

    connected :
      R453.ConnectedCorePathGeometry data

    observableSeparation :
      R450.CanonicalObservableToGraphSeparation data

    sourceAmplitudeBelow :
      R448.sourceAmplitude
        (R453.asCanonicalDomainSpecificRateSplit data connected)
      ≤ℝ
      embedQ ringEmbedding amplitude

    sourceResidualBelowGeometricPower :
      ∀ depth →
      R414.weight
        (R448.sourceDecay
          (R453.asCanonicalDomainSpecificRateSplit data connected))
        depth
      ≤ℝ
      embedQ ringEmbedding (Power.rationalPower ratio depth)

open GeneralGeometricTwoWilsonSource public

physicalDecay :
  ∀ {Measure Observable dataSet extension base data ringEmbedding amplitude ratio}
    (source :
      GeneralGeometricTwoWilsonSource
        {Measure = Measure}
        {Observable = Observable}
        {dataSet = dataSet}
        {extension = extension}
        {base = base}
        data ringEmbedding amplitude ratio) →
  R388.RationalPowerDistanceAntitone ratio →
  R451.CanonicalPhysicalDecayCalibration
    (R453.asCanonicalDomainSpecificRateSplit data (connected source))
physicalDecay
    {base = base} {data = data} {ringEmbedding = ringEmbedding}
    {ratio = ratio}
    source antitone = record
  { R451.CanonicalPhysicalDecayCalibration.euclideanTime =
      R318.physicalDistance base
        (R444.leftObservable data)
        (R444.rightObservable data)
  ; R451.CanonicalPhysicalDecayCalibration.physicalEnvelope =
      λ time →
        embedQ ringEmbedding (Power.rationalPower ratio time)
  ; R451.CanonicalPhysicalDecayCalibration.selectedResidualBelowPhysicalEnvelope =
      ≤ℝ-trans
        (sourceResidualBelowGeometricPower source
          (Graph.ymGraphDist
            (R444.leftMark data)
            (R444.rightMark data)))
        (Base.orderPreserving
          (orderedEmbedding ringEmbedding)
          (R388.powerAntitone antitone
            (R450.physicalDistanceBelowSelectedGraphDistance
              (observableSeparation source))))
  }

literalTheorem :
  ∀ {Measure Observable dataSet extension base data ringEmbedding amplitude ratio}
    (source :
      GeneralGeometricTwoWilsonSource
        {Measure = Measure}
        {Observable = Observable}
        {dataSet = dataSet}
        {extension = extension}
        {base = base}
        data ringEmbedding amplitude ratio) →
  R388.RationalPowerDistanceAntitone ratio →
  Literal.LiteralTwoWilsonMarkedExpansionTheorem
    {Measure = Measure}
    {Observable = Observable}
    {dataSet = dataSet}
    {extension = extension}
    {base = base}
    data
    (orderedEmbedding ringEmbedding)
literalTheorem source antitone = record
  { Literal.LiteralTwoWilsonMarkedExpansionTheorem.mixedLogResponse =
      mixedLog source
  ; Literal.LiteralTwoWilsonMarkedExpansionTheorem.connectedCore =
      connected source
  ; Literal.LiteralTwoWilsonMarkedExpansionTheorem.residualDecay =
      physicalDecay source antitone
  }

literalTwoWilsonEmbeddedGeneralGeometricDecay :
  ∀ {Measure Observable dataSet extension base data ringEmbedding amplitude ratio}
    (source :
      GeneralGeometricTwoWilsonSource
        {Measure = Measure}
        {Observable = Observable}
        {dataSet = dataSet}
        {extension = extension}
        {base = base}
        data ringEmbedding amplitude ratio)
    (amplitudeNN : 0ℚ ≤ amplitude)
    (ratioNN : 0ℚ ≤ ratio)
    (antitone : R388.RationalPowerDistanceAntitone ratio) →
  let time =
        R318.physicalDistance base
          (R444.leftObservable data)
          (R444.rightObservable data)
  in
  embedQ ringEmbedding
    (R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet
        (R445.cutoff (mixedLog source)))
      (R444.leftObservable data)
      (R444.rightObservable data))
  ≤ℝ
  embedQ ringEmbedding
    (amplitude * Power.rationalPower ratio time)
literalTwoWilsonEmbeddedGeneralGeometricDecay
    {base = base} {data = data} {ringEmbedding = ringEmbedding}
    {amplitude = amplitude} {ratio = ratio}
    source amplitudeNN ratioNN antitone =
  let
    geometry =
      R453.asCanonicalDomainSpecificRateSplit data (connected source)
    time =
      R318.physicalDistance base
        (R444.leftObservable data)
        (R444.rightObservable data)

    sourceBound =
      Literal.literalTwoWilsonEmbeddedCovarianceDecay
        (literalTheorem source antitone)

    powerNN =
      embeddedPowerNonnegative ringEmbedding ratio ratioNN time

    scaledAmplitude =
      mulMonotoneNonnegative
        (R448.sourceAmplitudeNonnegative geometry)
        (sourceAmplitudeBelow source)
        powerNN
        ≤ℝ-refl

    toEmbeddedProduct =
      ≤ℝ-trans sourceBound scaledAmplitude
  in
  subst
    (λ upper →
      embedQ ringEmbedding
        (R278.connectedCovarianceMagnitude extension
          (Gram.measureSequence dataSet
            (R445.cutoff (mixedLog source)))
          (R444.leftObservable data)
          (R444.rightObservable data))
      ≤ℝ upper)
    (sym
      (embeddedGeometricProductExact
        ringEmbedding amplitude ratio time))
    toEmbeddedProduct

record RationalImageOrderReflection
    (embedding : Ring.RationalRealRingEmbedding) : Set₁ where
  field
    reflectLessEqual :
      ∀ {left right : ℚ} →
      embedQ embedding left ≤ℝ embedQ embedding right →
      left ≤ right

open RationalImageOrderReflection public

record LiteralTwoWilsonGeneralGeometricFamily
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
    physicalDistance : Observable → Observable → Nat

    amplitude ratio : ℚ
    amplitudeNonnegative : 0ℚ ≤ amplitude
    ratioNonnegative : 0ℚ ≤ ratio
    ratioStrictlyBelowOne : ratio < 1ℚ

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
      GeneralGeometricTwoWilsonSource
        {Measure = Measure}
        {Observable = Observable}
        {dataSet = dataSet}
        {extension = extension}
        {base = base}
        (dataAt cutoff left right)
        ringEmbedding amplitude ratio

    leftObservableExact :
      ∀ cutoff left right →
      R444.leftObservable (dataAt cutoff left right) ≡ left

    rightObservableExact :
      ∀ cutoff left right →
      R444.rightObservable (dataAt cutoff left right) ≡ right

    cutoffExact :
      ∀ cutoff left right →
      R445.cutoff (mixedLog (sourceAt cutoff left right))
      ≡ cutoff

    physicalDistanceExact :
      ∀ cutoff left right →
      R318.physicalDistance base
        (R444.leftObservable (dataAt cutoff left right))
        (R444.rightObservable (dataAt cutoff left right))
      ≡ physicalDistance left right

    orderReflection :
      RationalImageOrderReflection ringEmbedding

open LiteralTwoWilsonGeneralGeometricFamily public

finiteCovarianceGeneralGeometricBound :
  ∀ {Measure Observable dataSet extension base ringEmbedding}
    (family :
      LiteralTwoWilsonGeneralGeometricFamily
        {Measure = Measure}
        {Observable = Observable}
        dataSet extension base ringEmbedding)
    cutoff left right →
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    left right
  ≤
  amplitude family
    * Power.rationalPower (ratio family)
        (physicalDistance family left right)
finiteCovarianceGeneralGeometricBound
    {extension = extension} {ringEmbedding = ringEmbedding}
    family cutoff left right =
  let
    data = dataAt family cutoff left right
    source = sourceAt family cutoff left right

    embedded =
      literalTwoWilsonEmbeddedGeneralGeometricDecay
        source
        (amplitudeNonnegative family)
        (ratioNonnegative family)
        (rationalPowerDistanceAntitoneFromStrictUnit
          (ratio family)
          (ratioNonnegative family)
          (ratioStrictlyBelowOne family))
  in
  reflectLessEqual (orderReflection family)
    (subst
      (λ selectedCutoff →
        embedQ ringEmbedding
          (R278.connectedCovarianceMagnitude extension
            (Gram.measureSequence dataSet selectedCutoff)
            left right)
        ≤ℝ
        embedQ ringEmbedding
          (amplitude family
            * Power.rationalPower (ratio family)
                (physicalDistance family left right)))
      (cutoffExact family cutoff left right)
      (subst
        (λ selectedLeft →
          embedQ ringEmbedding
            (R278.connectedCovarianceMagnitude extension
              (Gram.measureSequence dataSet
                (R445.cutoff (mixedLog source)))
              selectedLeft right)
          ≤ℝ
          embedQ ringEmbedding
            (amplitude family
              * Power.rationalPower (ratio family)
                  (physicalDistance family left right)))
        (leftObservableExact family cutoff left right)
        (subst
          (λ selectedRight →
            embedQ ringEmbedding
              (R278.connectedCovarianceMagnitude extension
                (Gram.measureSequence dataSet
                  (R445.cutoff (mixedLog source)))
                (R444.leftObservable data)
                selectedRight)
            ≤ℝ
            embedQ ringEmbedding
              (amplitude family
                * Power.rationalPower (ratio family)
                    (physicalDistance family left right)))
          (rightObservableExact family cutoff left right)
          (subst
            (λ selectedDistance →
              embedQ ringEmbedding
                (R278.connectedCovarianceMagnitude extension
                  (Gram.measureSequence dataSet
                    (R445.cutoff (mixedLog source)))
                  (R444.leftObservable data)
                  (R444.rightObservable data))
              ≤ℝ
              embedQ ringEmbedding
                (amplitude family
                  * Power.rationalPower (ratio family)
                      selectedDistance))
            (physicalDistanceExact family cutoff left right)
            embedded))))

asQuantitativeCorrelationDecayTrajectory :
  ∀ {Measure Observable dataSet extension base ringEmbedding} →
  (family :
    LiteralTwoWilsonGeneralGeometricFamily
      {Measure = Measure}
      {Observable = Observable}
      dataSet extension base ringEmbedding) →
  Unified.QuantitativeCorrelationDecayTrajectory
asQuantitativeCorrelationDecayTrajectory
    {dataSet = dataSet} {extension = extension} family = record
  { Unified.QuantitativeCorrelationDecayTrajectory.State = Nat
  ; Unified.QuantitativeCorrelationDecayTrajectory.Observable = _
  ; Unified.QuantitativeCorrelationDecayTrajectory.Correlation = Nat
  ; Unified.QuantitativeCorrelationDecayTrajectory.correlationProjection =
      λ cutoff → cutoff
  ; Unified.QuantitativeCorrelationDecayTrajectory.stateAtScale =
      λ cutoff → cutoff
  ; Unified.QuantitativeCorrelationDecayTrajectory.physicalDistance =
      physicalDistance family
  ; Unified.QuantitativeCorrelationDecayTrajectory.connectedCorrelationMagnitude =
      λ cutoff left right →
        R278.connectedCovarianceMagnitude extension
          (Gram.measureSequence dataSet cutoff)
          left right
  ; Unified.QuantitativeCorrelationDecayTrajectory.amplitude =
      amplitude family
  ; Unified.QuantitativeCorrelationDecayTrajectory.ratio =
      ratio family
  ; Unified.QuantitativeCorrelationDecayTrajectory.amplitudeNonnegative =
      amplitudeNonnegative family
  ; Unified.QuantitativeCorrelationDecayTrajectory.ratioNonnegative =
      ratioNonnegative family
  ; Unified.QuantitativeCorrelationDecayTrajectory.ratioStrictlyBelowOne =
      ratioStrictlyBelowOne family
  ; Unified.QuantitativeCorrelationDecayTrajectory.geometricDecayAtEveryScale =
      finiteCovarianceGeneralGeometricBound family
  }
