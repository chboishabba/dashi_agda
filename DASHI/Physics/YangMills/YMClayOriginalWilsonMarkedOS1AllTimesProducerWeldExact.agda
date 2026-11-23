module DASHI.Physics.YangMills.YMClayOriginalWilsonMarkedOS1AllTimesProducerWeldExact where

------------------------------------------------------------------------
-- P0 STEELMAN BIDI MAX-CUT, EXISTING SOURCE OWNERS ONLY:
--
--    Literal Wilson marked W1/W3 physical source (CMP119/T5)
--       -> original R556 finite selected Wilson covariance / R278
--       -> R551 same-family continuum clustering
--       -> one all-words/all-times R281 spectral correlation carrier.
--
-- Time comes ONLY from the original R332 OS1 Euclidean assembly. The
-- selected source physicalDistance is identified with R304's actual
-- pairwise Euclidean shell distance; no arbitrary metric quantifier.
--
-- THIS FILE PROVES COMPILER COMPOSITION, not any newly postulated
-- physical analytical bound. Original literal marked W1/W3 source,
-- original Wilson physical decoding, bounded F/G/FG, selected-metric
-- equality, finite-continuum measure laws and one reconstructed H_OS
-- are explicit independent proof-bearing inputs. Original real n=3
-- R445 Wilson measure vs rational R575 CMP119/T5 source is another
-- explicit same-source comparison. NO CLAY GAP CLAIM.
--
-- Kernel status: SOURCE WRITTEN, local Agda 2.9 unavailable.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.YangMillsRationalAbsoluteCovarianceExtensionRound575Exact as R575
import DASHI.Physics.YangMills.BalabanLiteralWilsonMarkedLocalizationSourceExact as Marked
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceRound556Exact as R556
import DASHI.Physics.YangMills.YangMillsWilsonContinuumClusteringRound551Exact as R551
import DASHI.Physics.YangMills.BalabanClayT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact as R304
import DASHI.Physics.YangMills.BalabanClayT5OS1RotationRestorationExact as OS1
import DASHI.Physics.YangMills.BalabanOSIndexedPairwiseEuclideanSemanticsRound332Exact as R332
import DASHI.Physics.YangMills.YMClayOriginalWilsonAllTimesOS1R556R281BIDIExact as BIDI
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

module _
    {Measure Observable Scale Volume Root Source Cluster Translation Rotation : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    (laws : R575.RationalCovarianceContinuityLaws dataSet)
    (marked : Marked.LiteralWilsonMarkedLocalizationSource
      {Scale = Scale} {Volume = Volume} {Root = Root}
      {Source = Source} {Cluster = Cluster}
      dataSet laws)
    (finite : R296.ExactT5JMagnitudePresentation
      dataSet (R575.rationalAbsoluteCovarianceExtension laws))
    (assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation Observable ℚ)
    (os : R332.OSIndexedPairwiseEuclideanSemantics
      {PhysicalObservable = Observable}
      {dataSet = dataSet}
      {extension = R575.rationalAbsoluteCovarianceExtension laws}
      {finite = finite} assembly)
  where

  originalOS1Translate : Observable → Nat → Observable
  originalOS1Translate word time =
    OS1.translate assembly (R332.timeTranslation os time) word

  -- Exactly the selected source geometry and selected test algebra;
  -- do NOT require time separation for every imaginable distance.
  record OriginalWilsonMarkedOS1PhysicalInputs : Set₁ where
    field
      decodedIsOriginalWord : ∀ word →
        R332.decode os word ≡ word

      selectedSourceDistanceIsR304 : ∀ left right →
        Marked.physicalDistance marked left right ≡
        R304.physicalDistance
          (R296.asDirectT5TwoSourceShell finite) left right

      leftBounded : ∀ word →
        Gram.BoundedObservable dataSet word

      translatedRightBounded : ∀ word time →
        Gram.BoundedObservable dataSet (originalOS1Translate word time)

      translatedProductBounded : ∀ left right time →
        Gram.BoundedObservable dataSet
          (Gram.multiplyObservable (Gram.operations dataSet)
            left (originalOS1Translate right time))

      upperOrderClosed :
        ∀ sequence target upper →
        Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
        (∀ cutoff → sequence cutoff ≤ upper) →
        target ≤ upper

  open OriginalWilsonMarkedOS1PhysicalInputs public

  -- Original R332 time-support proof, transported ONLY across the
  -- same R304/R556 source shell metric and original observable decoder.
  selectedOriginalMarkedDistanceIsEuclideanTime :
    (physical : OriginalWilsonMarkedOS1PhysicalInputs) →
    ∀ left right time →
    Marked.physicalDistance marked left
      (originalOS1Translate right time)
    ≡ time
  selectedOriginalMarkedDistanceIsEuclideanTime
      physical left right time =
    trans
      (selectedSourceDistanceIsR304 physical
        left (originalOS1Translate right time))
      (trans
        (cong₂
          (R304.physicalDistance
            (R296.asDirectT5TwoSourceShell finite))
          (sym (decodedIsOriginalWord physical left))
          (cong
            (OS1.translate assembly (R332.timeTranslation os time))
            (sym (decodedIsOriginalWord physical right))))
        (R332.supportDistanceIsTime os left right time))

  -- Corrected master-marked producer uses the SELECTED distance.
  -- This is actual construction of its downstream record, not
  -- a postulated independent "time is distance" theorem.
  originalWEXTDownstreamFromOS1 :
    OriginalWilsonMarkedOS1PhysicalInputs →
    Marked.WilsonWEXTDownstreamSemantics
      dataSet (Marked.physicalDistance marked)
  originalWEXTDownstreamFromOS1 physical = record
    { Marked.WilsonWEXTDownstreamSemantics.timeTranslate =
        originalOS1Translate
    ; Marked.WilsonWEXTDownstreamSemantics.leftBounded =
        leftBounded physical
    ; Marked.WilsonWEXTDownstreamSemantics.translatedRightBounded =
        translatedRightBounded physical
    ; Marked.WilsonWEXTDownstreamSemantics.translatedProductBounded =
        translatedProductBounded physical
    ; Marked.WilsonWEXTDownstreamSemantics.supportDistanceIsEuclideanTime =
        selectedOriginalMarkedDistanceIsEuclideanTime physical
    ; Marked.WilsonWEXTDownstreamSemantics.upperOrderClosed =
        upperOrderClosed physical
    }

  -- Core weld: literal original W1/W3 marked source + OS1 semantics
  -- enters the ALREADY EXISTING R556 rational Wilson covariance carrier.
  -- Analytic W1/W3 themselves remain the original source's premises.
  originalMarkedOS1CompilesToR556 :
    OriginalWilsonMarkedOS1PhysicalInputs →
    R556.IndexedSourceFirstWilsonCovarianceData
      {Scale = Scale} {Volume = Volume} {Root = Root}
      dataSet (R575.rationalAbsoluteCovarianceExtension laws)
  originalMarkedOS1CompilesToR556 physical =
    Marked.literalMarkedLocalizationCompilesToR556
      marked (originalWEXTDownstreamFromOS1 physical)

  -- No independent covariance convergence or new physical cluster
  -- theorem: existing R556 -> R551 proof, same original W1/W3 source.
  originalMarkedOS1ContinuumWilsonClustering :
    (physical : OriginalWilsonMarkedOS1PhysicalInputs) →
    ∀ left right time →
    R556.continuumCovariance
      (originalMarkedOS1CompilesToR556 physical)
      left right time
    ≤ Shell.quarter * Power.rationalPower Geo.half time
  originalMarkedOS1ContinuumWilsonClustering physical =
    BIDI.originalAllTimesSourceContinuumHalfRate
      (originalMarkedOS1CompilesToR556 physical)

  -- Reverse endpoint: one SAME all-pair/all-time selected source for R281
  -- without selecting a different spectral representation for each pair.
  originalMarkedOS1AllPairsTimes :
    (physical : OriginalWilsonMarkedOS1PhysicalInputs) →
    R278.SelectedConnectedCovarianceTests dataSet
  originalMarkedOS1AllPairsTimes physical =
    BIDI.originalAllWilsonPairsTimesTests
      (originalMarkedOS1CompilesToR556 physical)

  originalMarkedOS1SameSpectrumClustering :
    (physical : OriginalWilsonMarkedOS1PhysicalInputs) →
    ∀ {SpectralObservable Energy}
      (spectrum : R281.ContinuumCovarianceSpectrumData
        {SpectralObservable = SpectralObservable}
        {Energy = Energy}
        dataSet (R575.rationalAbsoluteCovarianceExtension laws)
        (originalMarkedOS1AllPairsTimes physical)) →
      BIDI.SameOSAllWilsonPairsTimesSpectrum
        (originalMarkedOS1CompilesToR556 physical) spectrum →
    ∀ observable time →
    Gap.connectedCorrelation
      (R281.asReconstructedClusteringSpectrum spectrum)
      observable time
    ≤ Shell.quarter * Power.rationalPower Geo.half time
  originalMarkedOS1SameSpectrumClustering
      physical spectrum indexCorrect =
    BIDI.originalAllWilsonPairsTimesSameR281SpectrumHasClustering
      (originalMarkedOS1CompilesToR556 physical)
      spectrum indexCorrect

-- Terminal gap NOT proved here. In particular:
-- * marked original Wilson two-support W1/W3 physical estimates;
-- * original real Wilson R445 to rational CMP119/T5 semantic identity;
-- * E1 continuum/OS positive complex Hilbert/nontriviality;
-- * spectrum above is the SAME actual H_OS for dense vacuum states;
-- * physical-unit m>0 for G1 all groups; all remain explicit.
