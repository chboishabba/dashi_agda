module DASHI.Physics.Foundations.RFCalibrationSourceAtlasExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- ARRAY CALIBRATION / PHASE-QUANTISATION SOURCE ATLAS
--
-- These sources pay bounded relationships among channel gain/phase mismatch,
-- array calibration, mutual coupling, phase-shifter quantisation and degraded
-- angular/beamforming performance.  They do not identify historical hardware,
-- exact emitter state, or operational use.
------------------------------------------------------------------------

wanPartialCalibrationPrimary : Source.AttributedSource
wanPartialCalibrationPrimary = Source.mkDOISource
  "Huan Wan; Bin Liao"
  "Fourth-order direction finding in antenna arrays with partial channel gain/phase calibration"
  "Signal Processing 169, 107380"
  "2020"
  "10.1016/j.sigpro.2019.107380"
  "https://doi.org/10.1016/j.sigpro.2019.107380"
  Source.academicArticleSource
  "primary source paying the bounded claim that channel gain/phase mismatch is a calibration error relevant to direction finding and that partial calibration changes the DOA-estimation problem"
  Source.publicAttribution

liJointCalibrationPrimary : Source.AttributedSource
liJointCalibrationPrimary = Source.mkDOISource
  "Jianfeng Li; Ji Ding; Defu Jiang"
  "Joint direction finding and array calibration method for MIMO radar with unknown gain phase errors"
  "IET Microwaves, Antennas & Propagation 10(14), 1563-1569"
  "2016"
  "10.1049/iet-map.2016.0104"
  "https://doi.org/10.1049/iet-map.2016.0104"
  Source.academicArticleSource
  "primary source paying the bounded relationship between unknown gain/phase errors and joint direction-finding plus array-calibration estimation"
  Source.publicAttribution

singhCouplingReview : Source.AttributedSource
singhCouplingReview = Source.mkDOISource
  "Himanshu Singh; Harish Kumar; Ravi Kumar"
  "Mutual Coupling in Phased Arrays: A Review"
  "International Journal of Antennas and Propagation 2013, 348123"
  "2013"
  "10.1155/2013/348123"
  "https://doi.org/10.1155/2013/348123"
  Source.academicArticleSource
  "review source paying the bounded claim that mutual coupling perturbs impedance, reflection coefficients, steering-vector behavior and DOA-estimation competence"
  Source.publicAttribution

kamodaQuantizationPrimary : Source.AttributedSource
kamodaQuantizationPrimary = Source.mkDOISource
  "Hiroyuki Kamoda; Fumiyasu Suginoshita"
  "A study on antenna gain degradation due to digital phase shifter in phased array antennas"
  "Microwave and Optical Technology Letters"
  "2011"
  "10.1002/mop.26145"
  "https://doi.org/10.1002/mop.26145"
  Source.academicArticleSource
  "primary source paying the bounded claim that finite phase-shifter quantisation introduces phase error and can degrade phased-array gain"
  Source.publicAttribution

ieiceQuantizationPrimary : Source.AttributedSource
ieiceQuantizationPrimary = Source.mkDOISource
  "IEICE Transactions on Communications authors"
  "Effect of Phase Shifter Quantization Error on the Performance of Millimeter Wave Beam Steering"
  "IEICE Transactions on Communications E100.B(10), 1884-1890"
  "2017"
  "10.1587/transcom.2016EBP3417"
  "https://doi.org/10.1587/transcom.2016EBP3417"
  Source.academicArticleSource
  "primary source paying the bounded claim that limited phase-shifter precision creates phase-quantisation error and beam-steering gain loss"
  Source.publicAttribution

rfCalibrationAtlas : Source.AttributedSourceAtlas
rfCalibrationAtlas = Source.mkSourceAtlas
  "RF array calibration / phase-quantisation source atlas"
  "DASHI.Physics.Foundations.RFCalibrationSourceAtlasExact"
  (wanPartialCalibrationPrimary ∷ liJointCalibrationPrimary ∷ singhCouplingReview ∷ kamodaQuantizationPrimary ∷ ieiceQuantizationPrimary ∷ [])
  "sources pay bounded calibration/error relationships only; historical instrument identity, exact bearing truth, exact world recovery and operational authority remain separate"
