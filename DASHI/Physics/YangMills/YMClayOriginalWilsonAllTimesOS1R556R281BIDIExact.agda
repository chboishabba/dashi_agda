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

  -- Preserve the whole Nat-indexed family in R281, not an individual
  -- singleton index for each time (which would fail the SAME-H BIDI).
  record SameSpectrumAllTimesSelectedIndex
      {SpectralObservable Energy : Set}
      (left right : Observable)
      (spectrum : R281.ContinuumCovarianceSpectrumData
        {SpectralObservable = SpectralObservable}
        {Energy = Energy}
        dataSet extension (originalAllTimesWilsonTests left right))
      : Set where
    field
      indexIsThisEuclideanTime : ∀ observable time →
        R281.indexFor spectrum observable time ≡ time

  open SameSpectrumAllTimesSelectedIndex public

  originalAllTimesSameR281Correlation :
    ∀ {SpectralObservable Energy}
      (left right : Observable)
      (spectrum : R281.ContinuumCovarianceSpectrumData
        {SpectralObservable = SpectralObservable}
        {Energy = Energy}
        dataSet extension (originalAllTimesWilsonTests left right)) →
    SameSpectrumAllTimesSelectedIndex left right spectrum →
    ∀ observable time →
    R556.continuumCovariance source left right time
    ≡ Gap.connectedCorrelation
        (R281.asReconstructedClusteringSpectrum spectrum)
        observable time
  originalAllTimesSameR281Correlation left right spectrum indexWeld
      observable time =
    trans
      (cong
        (λ index →
          R278.connectedCovarianceMagnitude extension
            (Gram.continuumMeasure dataSet)
            (R278.left (originalAllTimesWilsonTests left right) index)
            (R278.right (originalAllTimesWilsonTests left right) index))
        (sym (indexIsThisEuclideanTime indexWeld observable time)))
      (R281.continuumCovarianceIsSpectrumCorrelation
        spectrum observable time)

  originalAllTimesSameR281SpectrumHasClustering :
    ∀ {SpectralObservable Energy}
      (left right : Observable)
      (spectrum : R281.ContinuumCovarianceSpectrumData
        {SpectralObservable = SpectralObservable}
        {Energy = Energy}
        dataSet extension (originalAllTimesWilsonTests left right)) →
    SameSpectrumAllTimesSelectedIndex left right spectrum →
    ∀ observable time →
    Gap.connectedCorrelation
      (R281.asReconstructedClusteringSpectrum spectrum)
      observable time
    ≤ Shell.quarter * Power.rationalPower Geo.half time
  originalAllTimesSameR281SpectrumHasClustering
      left right spectrum indexWeld observable time =
    subst
      (λ value → value ≤
        Shell.quarter * Power.rationalPower Geo.half time)
      (originalAllTimesSameR281Correlation
        left right spectrum indexWeld observable time)
      (originalAllTimesSourceContinuumHalfRate left right time)

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
