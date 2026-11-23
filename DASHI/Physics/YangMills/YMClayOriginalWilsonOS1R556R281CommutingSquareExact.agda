module DASHI.Physics.YangMills.YMClayOriginalWilsonOS1R556R281CommutingSquareExact where

------------------------------------------------------------------------
-- P0 source-first BIDI COMMUTING SQUARE:
--
--                           same ORIGINAL Wilson word/pair/time
--                        + OS1 translation / selected R556 time carrier
--                                           |
--   R556 translated F,G -- pointwise --> OS1 Euclidean-translated F,G
--           |                                         |
--   actual R278 finite                          SAME R278 finite
--   covariance at cutoff                        covariance at cutoff
--           |                                         |
--   R278 same-family limit                   R278 same-family limit
--           |                                         |
--   ONE continuum covariance -- same INDEX --> ONE R281 spectrum corr.
--
-- This is NOT a second measure, scalar, Hilbert space or Hamiltonian.
-- Source shift identity is from original R332/R556 geometry WELD.
-- Spectrum selection is ONE R281 all-pairs/all-times source.
-- Published Wilson RP/complex OS/H_OS and original real R445 -> rational
-- R575/T5 changing-cutoff identification are still PHYSICAL OPEN inputs.
--
-- Care: R278's Converges predicate is abstract. We prove the finite
-- pointwise and continuum equalities, and call the ORIGINAL R278
-- convergence on the R556 path. Promoting it to a convergence property
-- for an extensionally equal OS1 *function sequence* requires that
-- predicate's own sequence-congruence law; never assume funext.
-- Source-written; Agda kernel NOT YET CHECKED.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanClayT5OS1RotationRestorationExact as OS1
import DASHI.Physics.YangMills.BalabanOSIndexedPairwiseEuclideanSemanticsRound332Exact as R332
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceExact as R556
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.YMClayOriginalWilsonAllTimesOS1R556R281BIDIExact as BIDI

module _
  {Measure Observable Scale Volume Root Translation Rotation : Set}
  {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
  {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
  (source : R556.IndexedSourceFirstWilsonCovarianceData
    {Scale = Scale} {Volume = Volume} {Root = Root}
    dataSet extension)
  {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
  (assembly : OS1.EuclideanCovarianceAssembly
    Translation Rotation Observable ℚ)
  (os1 : R332.OSIndexedPairwiseEuclideanSemantics
    {PhysicalObservable = Observable}
    {dataSet = dataSet} {extension = extension} {finite = finite}
    assembly)
  (weld : BIDI.SameOriginalOS1R556TimeGeometry assembly os1 source)
  where

  sourceTimeTranslate : Observable → Nat → Observable
  sourceTimeTranslate = R556.timeTranslate source

  originalOS1TimeTranslate : Observable → Nat → Observable
  originalOS1TimeTranslate word time =
    OS1.translate assembly (R332.timeTranslation os1 time) word

  -- Upper horizontal arrow of the original source square.
  originalWilsonTimeTranslationSquare :
    ∀ word time →
    sourceTimeTranslate word time ≡
    originalOS1TimeTranslate word time
  originalWilsonTimeTranslationSquare word time =
    BIDI.sourceShiftIsOS1 weld word time

  originalWilsonFiniteCovariance :
    Nat → Observable → Observable → Nat → ℚ
  originalWilsonFiniteCovariance cutoff left right time =
    R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet cutoff)
      left (sourceTimeTranslate right time)

  originalWilsonOS1FiniteCovariance :
    Nat → Observable → Observable → Nat → ℚ
  originalWilsonOS1FiniteCovariance cutoff left right time =
    R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet cutoff)
      left (originalOS1TimeTranslate right time)

  -- Both sides use the IDENTICAL original finite CMP119/T5 state.
  -- Only the original source-owned OS1/translated-observable map changes.
  originalFiniteCovarianceSquare :
    ∀ cutoff left right time →
    originalWilsonFiniteCovariance cutoff left right time ≡
    originalWilsonOS1FiniteCovariance cutoff left right time
  originalFiniteCovarianceSquare cutoff left right time =
    cong
      (R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff) left)
      (originalWilsonTimeTranslationSquare right time)

  originalWilsonOS1ContinuumCovariance :
    Observable → Observable → Nat → ℚ
  originalWilsonOS1ContinuumCovariance left right time =
    R278.connectedCovarianceMagnitude extension
      (Gram.continuumMeasure dataSet)
      left (originalOS1TimeTranslate right time)

  -- Continuum horizontal equality: SAME continuum original CMP119/T5
  -- state, no independent equality of unrelated covariance limits.
  originalContinuumCovarianceSquare :
    ∀ left right time →
    R556.continuumCovariance source left right time ≡
    originalWilsonOS1ContinuumCovariance left right time
  originalContinuumCovarianceSquare left right time =
    cong
      (R278.connectedCovarianceMagnitude extension
        (Gram.continuumMeasure dataSet) left)
      (originalWilsonTimeTranslationSquare right time)

  -- The vertical finite->continuum arrow is the ALREADY EXISTING R278
  -- source theorem, on ONE all-pairs/time indexed R556 family.
  originalSourceFiniteContinuumConverges :
    ∀ left right time →
    Gram.Converges (Gram.scalarConvergence dataSet)
      (λ cutoff →
        originalWilsonFiniteCovariance cutoff left right time)
      (R556.continuumCovariance source left right time)
  originalSourceFiniteContinuumConverges left right time =
    BIDI.originalAllWilsonPairsTimesConverge
      source left right time

  originalSelectedSourceDistanceTime :
    ∀ left right time →
    R556.physicalDistance source left
      (sourceTimeTranslate right time) ≡ time
  originalSelectedSourceDistanceTime =
    BIDI.originalWilsonSourceDistanceIsSameOS1Time weld

  -- SAME ONE R281 spectrum for every selected original Wilson
  -- (left,right,time), not a family of unrelated spectra indexed by t.
  -- The dictionary is exactly the existing all-pairs/time R281 index.
  originalOS1SquareEndsInSameR281Spectrum :
    ∀ {SpectralObservable Energy}
      (spectrum : R281.ContinuumCovarianceSpectrumData
        {SpectralObservable = SpectralObservable}
        {Energy = Energy}
        dataSet extension (BIDI.originalAllWilsonPairsTimesTests source))
      (dictionary : BIDI.SameOSAllWilsonPairsTimesSpectrum source spectrum)
      observable time →
    let selected = BIDI.spectralWilsonPair dictionary observable in
    originalWilsonOS1ContinuumCovariance
      (proj₁ selected) (proj₂ selected) time
    ≡
    Gap.connectedCorrelation
      (R281.asReconstructedClusteringSpectrum spectrum)
      observable time
  originalOS1SquareEndsInSameR281Spectrum spectrum dictionary
      observable time =
    let selected = BIDI.spectralWilsonPair dictionary observable in
    trans
      (sym
        (originalContinuumCovarianceSquare
          (proj₁ selected) (proj₂ selected) time))
      (BIDI.originalAllWilsonPairsTimesSameR281Correlation
        source spectrum dictionary observable time)

  -- The square on this original rational physical carrier closes
  -- as equality of source observables and finite/continuum covariance
  -- coordinates, conditional on the EXACT original OS1 geometry and
  -- ONE R281 spectral dictionary. It does not claim the physical
  -- representation on the same reconstructed H_OS: that is the
  -- already-original P3 physical spectrum-identification gate.

-- Remaining FIRST external square: original real SU(N) n=3 R445 Gibbs
-- vs source-rational changing-cutoff CMP119/T5 carrier. Its physical
-- same-measure scalar/mark compatibility is NOT supplied by this file.
-- P0 E1/D1/D2/N1/G1 remain OPEN.
