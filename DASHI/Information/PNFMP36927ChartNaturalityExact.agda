module DASHI.Information.PNFMP36927ChartNaturalityExact where

-- Reuse the *actual* PNF Marchenko-Pastur band and existing classifier
-- on the existing trialectic 3-chart cover, with 369/27 carriers kept
-- as formal chart geometry, not confused with the sample observation count.
--
-- A pointwise threshold commutes with overlap-compatible gluing.
-- A newly computed covariance spectrum is NOT pointwise, so this
-- theorem does not assert that local MP estimates reconstruct a global
-- Marchenko-Pastur law or a globally PSD covariance.

open import Agda.Builtin.Equality using (_≡_)
import DASHI.Information.PNFSpectralGeometry as PNF
import DASHI.Information.PNFMarchenkoPasturFiniteExact as MP
import DASHI.Information.PNFTrialecticSpectralDescentExact as Charts
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer

mpClassifyObserver :
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (classifier : PNF.NoiseClassifier K (MP.calibratedMPBand K C)) →
  Observer.ObserverMatrix3 (PNF.ScalarStructure.Scalar K) →
  Observer.ObserverMatrix3 PNF.SpectralClass
mpClassifyObserver K C classifier =
  Charts.mapObserver (PNF.NoiseClassifier.classify classifier)

mpClassificationCommutesWith369Gluing :
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (classifier : PNF.NoiseClassifier K (MP.calibratedMPBand K C)) →
  (family : Charts.SpectralMatchingFamily (PNF.ScalarStructure.Scalar K)) →
  mpClassifyObserver K C classifier (Charts.glueSpectral family)
  ≡
  Charts.glueSpectral
    (Charts.mapMatchingFamily
      (PNF.NoiseClassifier.classify classifier) family)
mpClassificationCommutesWith369Gluing K C classifier family =
  Charts.pointwiseSpectralClassificationCommutesWithGluing
    (PNF.NoiseClassifier.classify classifier) family

mpClassifiedChartABAgreesWithGlobal :
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (classifier : PNF.NoiseClassifier K (MP.calibratedMPBand K C)) →
  (global : Observer.ObserverMatrix3 (PNF.ScalarStructure.Scalar K)) →
  Charts.abOf (mpClassifyObserver K C classifier global)
  ≡
  Charts.mapAB (PNF.NoiseClassifier.classify classifier)
    (Charts.abOf global)
mpClassifiedChartABAgreesWithGlobal K C classifier global =
  Charts.pointwiseSpectralClassificationCommutesWithAB
    (PNF.NoiseClassifier.classify classifier) global

mpClassifiedChartBCAgreesWithGlobal :
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (classifier : PNF.NoiseClassifier K (MP.calibratedMPBand K C)) →
  (global : Observer.ObserverMatrix3 (PNF.ScalarStructure.Scalar K)) →
  Charts.bcOf (mpClassifyObserver K C classifier global)
  ≡
  Charts.mapBC (PNF.NoiseClassifier.classify classifier)
    (Charts.bcOf global)
mpClassifiedChartBCAgreesWithGlobal K C classifier global =
  Charts.pointwiseSpectralClassificationCommutesWithBC
    (PNF.NoiseClassifier.classify classifier) global

mpClassifiedChartCAAgreesWithGlobal :
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (classifier : PNF.NoiseClassifier K (MP.calibratedMPBand K C)) →
  (global : Observer.ObserverMatrix3 (PNF.ScalarStructure.Scalar K)) →
  Charts.caOf (mpClassifyObserver K C classifier global)
  ≡
  Charts.mapCA (PNF.NoiseClassifier.classify classifier)
    (Charts.caOf global)
mpClassifiedChartCAAgreesWithGlobal K C classifier global =
  Charts.pointwiseSpectralClassificationCommutesWithCA
    (PNF.NoiseClassifier.classify classifier) global
