module DASHI.Physics.YangMills.YMClayOriginalWilsonAllTimesOS1R556R281BIDIExact where

------------------------------------------------------------------------
-- P0 WELD-FORWARD: ORIGINAL EXISTING PRODUCERS, ONE ALL-TIME CARRIER.
--
-- Reverse endpoint: an OS spectrum must see the SAME Wilson covariance
-- for EVERY Euclidean time, not a fresh one-point test family at each t.
--
-- Forward owner on master: R556 -> R278 -> R491 -> R551; R332 -> OS1;
-- continuum R281 and P3 own SAME-spectrum correlation construction.
--
-- Crucial geometry: R332's OS1 time translation and R556's translation
-- must agree on the SAME observable; original R304 pairwise Euclidean
-- distance must be the SAME R556 source distance.  Prove the support-time
-- theorem by composing those exact owners, not by inventing a clock.
--
-- CRITICAL BOUNDARIES:
--   * this module uses R556's RATIONAL scalar and CMP119/T5 carrier.
--   * original R445 finite Wilson expectations use REAL scalar; a genuine
--     same-source scalar/measure and changing-cutoff carrier comparison
--     remains OPEN; do not silently identify ℚ and ℝ.
--   * the physical R491 WEXT shell, bounded original tests, exact OS1
--     geometry dictionary, R278 continuum and OS Hamiltonian relation
--     must be supplied by their existing producers.
--   * the R281 spectral producer is a physical hypothesis; its
--     continuum-covariance correlation is definitional only AFTER
--     that spectrum is constructed. No Clay terminal claim.
-- SOURCE-WRITTEN; NEW MODULE NOT YET AGDA KERNEL CHECKED.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; subst)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact as R304
import DASHI.Physics.YangMills.BalabanClayT5OS1RotationRestorationExact as OS1
import DASHI.Physics.YangMills.BalabanOSIndexedPairwiseEuclideanSemanticsRound332Exact as R332
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceRound556Exact as R556
import DASHI.Physics.YangMills.YangMillsWilsonContinuumClusteringRound551Exact as R551
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

module _
  {Measure Observable Scale Volume Root : Set}
  {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
  {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
  (source : R556.IndexedSourceFirstWilsonCovarianceData
    {Scale = Scale} {Volume = Volume} {Root = Root}
    dataSet extension)
  where

  -- R556 originally constructs one singleton-index pairTests per time.
  -- The physical OS spectrum must instead have ONE common carrier with
  -- the SAME source left word and ALL translated right words.
  -- No extra analytic estimate; reuse its already-selected boundedness.
  originalAllTimesWilsonTests :
    (left right : Observable) →
    R278.SelectedConnectedCovarianceTests dataSet
  originalAllTimesWilsonTests left right = record
    { R278.SelectedConnectedCovarianceTests.Index = Nat
    ; R278.SelectedConnectedCovarianceTests.left = λ time → left
    ; R278.SelectedConnectedCovarianceTests.right =
        λ time → R556.timeTranslate source right time
    ; R278.SelectedConnectedCovarianceTests.leftBounded =
        λ time → R556.leftBounded source left
    ; R278.SelectedConnectedCovarianceTests.rightBounded =
        λ time → R556.translatedRightBounded source right time
    ; R278.SelectedConnectedCovarianceTests.productBounded =
        λ time → R556.translatedProductBounded source left right time
    }

  -- One actual CMP119/T5 continuum measure, one selected test family,
  -- all Euclidean times: R278 already proves this convergence.
  originalAllTimesSourceCovarianceConverges :
    ∀ left right time →
    Gram.Converges (Gram.scalarConvergence dataSet)
      (λ cutoff →
        R278.connectedCovarianceMagnitude extension
          (Gram.measureSequence dataSet cutoff)
          left (R556.timeTranslate source right time))
      (R278.connectedCovarianceMagnitude extension
        (Gram.continuumMeasure dataSet)
        left (R556.timeTranslate source right time))
  originalAllTimesSourceCovarianceConverges left right time =
    R278.selectedConnectedCovarianceMagnitudeConverges
      extension (originalAllTimesWilsonTests left right) time

  -- The physical source R556 finite Wilson WEXT estimate plus R551
  -- supplies the continuum half-rate bound; this is NOT a NEW
  -- CMP116/119 estimate, and cannot inhabit the R556 source unaided.
  originalAllTimesSourceContinuumHalfRate :
    ∀ left right time →
    R556.continuumCovariance source left right time
    ≤ Shell.quarter * Power.rationalPower Geo.half time
  originalAllTimesSourceContinuumHalfRate left right time =
    R551.continuumWilsonHalfRateBound
      (R556.indexedAsContinuumClustering source)
      left right time

  -- Reverse-side correction: a separate R281 spectrum for each
  -- Wilson pair would STILL be insufficient for ONE physical H on
  -- a norm-dense family. Use a SINGLE all-pairs/all-times test family
  -- on the SAME R556/Gram/R278 measure, with INDEX
  -- ((left Wilson observable, right Wilson observable), Euclidean time).
  -- This is the smallest actual shared-index carrier for the D2 cut.
  originalAllWilsonPairsTimesTests :
    R278.SelectedConnectedCovarianceTests dataSet
  originalAllWilsonPairsTimesTests = record
    { R278.SelectedConnectedCovarianceTests.Index =
        (Observable × Observable) × Nat
    ; R278.SelectedConnectedCovarianceTests.left =
        λ index → proj₁ (proj₁ index)
    ; R278.SelectedConnectedCovarianceTests.right =
        λ index →
          R556.timeTranslate source (proj₂ (proj₁ index)) (proj₂ index)
    ; R278.SelectedConnectedCovarianceTests.leftBounded =
        λ index → R556.leftBounded source (proj₁ (proj₁ index))
    ; R278.SelectedConnectedCovarianceTests.rightBounded =
        λ index →
          R556.translatedRightBounded source
            (proj₂ (proj₁ index)) (proj₂ index)
    ; R278.SelectedConnectedCovarianceTests.productBounded =
        λ index →
          R556.translatedProductBounded source
            (proj₁ (proj₁ index)) (proj₂ (proj₁ index))
            (proj₂ index)
    }

  -- The same R278 continuum convergence proof now runs for ALL
  -- pairs and times from this one fixed original measure carrier.
  originalAllWilsonPairsTimesConverge :
    ∀ left right time →
    Gram.Converges (Gram.scalarConvergence dataSet)
      (λ cutoff →
        R278.connectedCovarianceMagnitude extension
          (Gram.measureSequence dataSet cutoff)
          left (R556.timeTranslate source right time))
      (R278.connectedCovarianceMagnitude extension
        (Gram.continuumMeasure dataSet)
        left (R556.timeTranslate source right time))
  originalAllWilsonPairsTimesConverge left right time =
    R278.selectedConnectedCovarianceMagnitudeConverges
      extension originalAllWilsonPairsTimesTests ((left , right) , time)

  -- The ONE R281 spectrum source must index exactly the same
  -- selected original Wilson word pair and time. The spectral
  -- presentation, subgap lower envelope and common OS H remain
  -- actual physical premises; no independent H is manufactured.
  record SameOSAllWilsonPairsTimesSpectrum
      {SpectralObservable Energy : Set}
      (spectrum : R281.ContinuumCovarianceSpectrumData
        {SpectralObservable = SpectralObservable}
        {Energy = Energy}
        dataSet extension originalAllWilsonPairsTimesTests)
      : Set where
    field
      spectralWilsonPair : SpectralObservable → Observable × Observable
      indexForUsesSamePairAndTime : ∀ observable time →
        R281.indexFor spectrum observable time
          ≡ ((spectralWilsonPair observable) , time)

  open SameOSAllWilsonPairsTimesSpectrum public

  originalAllWilsonPairsTimesSameR281Correlation :
    ∀ {SpectralObservable Energy}
      (spectrum : R281.ContinuumCovarianceSpectrumData
        {SpectralObservable = SpectralObservable}
        {Energy = Energy}
        dataSet extension originalAllWilsonPairsTimesTests) →
    (dictionary : SameOSAllWilsonPairsTimesSpectrum spectrum) →
    ∀ observable time →
    let selected = spectralWilsonPair dictionary observable in
    R556.continuumCovariance source
      (proj₁ selected) (proj₂ selected) time
    ≡ Gap.connectedCorrelation
        (R281.asReconstructedClusteringSpectrum spectrum)
        observable time
  originalAllWilsonPairsTimesSameR281Correlation
      spectrum dictionary observable time =
    trans
      (cong
        (λ index →
          R278.connectedCovarianceMagnitude extension
            (Gram.continuumMeasure dataSet)
            (R278.left originalAllWilsonPairsTimesTests index)
            (R278.right originalAllWilsonPairsTimesTests index))
        (sym (indexForUsesSamePairAndTime
          dictionary observable time)))
      (R281.continuumCovarianceIsSpectrumCorrelation
        spectrum observable time)

  originalAllWilsonPairsTimesSameR281SpectrumHasClustering :
    ∀ {SpectralObservable Energy}
      (spectrum : R281.ContinuumCovarianceSpectrumData
        {SpectralObservable = SpectralObservable}
        {Energy = Energy}
        dataSet extension originalAllWilsonPairsTimesTests) →
    SameOSAllWilsonPairsTimesSpectrum spectrum →
    ∀ observable time →
    Gap.connectedCorrelation
      (R281.asReconstructedClusteringSpectrum spectrum)
      observable time
    ≤ Shell.quarter * Power.rationalPower Geo.half time
  originalAllWilsonPairsTimesSameR281SpectrumHasClustering
      spectrum dictionary observable time =
    let selected = spectralWilsonPair dictionary observable in
    subst
      (λ value → value ≤
        Shell.quarter * Power.rationalPower Geo.half time)
      (originalAllWilsonPairsTimesSameR281Correlation
        spectrum dictionary observable time)
      (originalAllTimesSourceContinuumHalfRate
        (proj₁ selected) (proj₂ selected) time)

-- The OS1/Euclidean distance end is ALREADY proven conditionally
-- on master in R332 and R304; construct their joint source identity,
-- rather than invent a second notion of "Euclidean time".
record SameOriginalOS1R556TimeGeometry
    {Measure Observable Scale Volume Root Translation Rotation : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation Observable ℚ)
    (semantics : R332.OSIndexedPairwiseEuclideanSemantics
      {PhysicalObservable = Observable}
      {dataSet = dataSet} {extension = extension} {finite = finite}
      assembly)
    (source : R556.IndexedSourceFirstWilsonCovarianceData
      {Scale = Scale} {Volume = Volume} {Root = Root}
      dataSet extension)
    : Set₁ where
  field
    -- Physical original-Wilson source decoder, not an unrelated T5 mark.
    decodedIsOriginalWilson : ∀ word →
      R332.decode semantics word ≡ word

    -- R556 time shift is literally the same translation as OS1.
    sourceShiftIsOS1 : ∀ word time →
      R556.timeTranslate source word time ≡
      OS1.translate assembly (R332.timeTranslation semantics time) word

    -- R556's physical shell metric is R304's selected source metric.
    sourceDistanceIsR304 : ∀ left right →
      R556.physicalDistance source left right ≡
      R304.physicalDistance (R296.asDirectT5TwoSourceShell finite)
        left right

open SameOriginalOS1R556TimeGeometry public

originalWilsonSourceDistanceIsSameOS1Time :
  ∀ {Measure Observable Scale Volume Root Translation Rotation}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation Observable ℚ}
    {semantics : R332.OSIndexedPairwiseEuclideanSemantics
      {PhysicalObservable = Observable}
      {dataSet = dataSet} {extension = extension} {finite = finite}
      assembly}
    {source : R556.IndexedSourceFirstWilsonCovarianceData
      {Scale = Scale} {Volume = Volume} {Root = Root}
      dataSet extension} →
  SameOriginalOS1R556TimeGeometry assembly semantics source →
  ∀ left right time →
  R556.physicalDistance source left
    (R556.timeTranslate source right time)
  ≡ time
originalWilsonSourceDistanceIsSameOS1Time
    {finite = finite} {assembly = assembly}
    {semantics = semantics} {source = source}
    weld left right time =
  trans
    (cong (R556.physicalDistance source left)
      (sourceShiftIsOS1 weld right time))
    (trans
      (sourceDistanceIsR304 weld left
        (OS1.translate assembly
          (R332.timeTranslation semantics time) right))
      (trans
        (cong₂
          (R304.physicalDistance
            (R296.asDirectT5TwoSourceShell finite))
          (sym (decodedIsOriginalWilson weld left))
          (cong
            (OS1.translate assembly
              (R332.timeTranslation semantics time))
            (sym (decodedIsOriginalWilson weld right))))
        (R332.supportDistanceIsTime semantics left right time)))

-- The only new proof above is a literal equality composition between
-- SOURCE-OWNED Euclidean translations and SOURCE-OWNED shell distances.
-- SAME E1 Wilson measure, real↔rational interpretation, physical WEXT,
-- OS positivity and actual one-H reconstructed spectrum remain OPEN.
