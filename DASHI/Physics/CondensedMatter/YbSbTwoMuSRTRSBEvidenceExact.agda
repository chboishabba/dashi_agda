module DASHI.Physics.CondensedMatter.YbSbTwoMuSRTRSBEvidenceExact where

------------------------------------------------------------------------
-- Source-scoped muSR evidence carrier for YbSb2.
--
-- Kataria et al. (PRL accepted 3 Aug 2026; DOI 10.1103/drzq-lfn5)
-- report:
--
-- * ZF-muSR spectra at 1.5 K and 0.1 K;
-- * a damped Gaussian Kubo-Toyabe form with nuclear rate Delta and
--   additional electronic rate Lambda;
-- * Lambda increasing below Tc while Delta is approximately constant;
-- * a small LF (~10 mT) decoupling the relaxation, supporting a
--   static/quasistatic source;
-- * dLambda = gamma_mu B_in and B_in approximately 0.44(3) G.
--
-- This file keeps those experimental/model-identification coordinates
-- distinct from the INT order-parameter theorem.  It does NOT prove that
-- a particular microscopic order parameter caused the measured field.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

data TemperatureTag : Set where
  kelvinOnePointFive kelvinZeroPointOne : TemperatureTag

data FieldTag : Set where
  zeroApplied longitudinalTenMilliTesla : FieldTag

data Rate : Set where
  lambdaNormal lambdaSuperconducting
  deltaNormal deltaSuperconducting : Rate

-- Source-scoped qualitative ordering: only the reported electronic
-- increase is inhabited here.
data RateIncrease : Rate → Rate → Set where
  lambdaIncrease :
    RateIncrease lambdaNormal lambdaSuperconducting

-- Approximate experimental equality is kept distinct from definitional
-- equality.  The paper reports nuclear Delta as approximately constant.
data ApproximatelyEqualRate : Rate → Rate → Set where
  nuclearStable :
    ApproximatelyEqualRate deltaNormal deltaSuperconducting

data Spectrum : TemperatureTag → FieldTag → Set where
  zfNormal :
    Spectrum kelvinOnePointFive zeroApplied
  zfSuperconducting :
    Spectrum kelvinZeroPointOne zeroApplied
  lfSuperconducting :
    Spectrum kelvinZeroPointOne longitudinalTenMilliTesla

data StaticDecouplingEvidence : Set where
  tenMilliTeslaDecouples : StaticDecouplingEvidence

data InternalFieldEstimate : Set where
  gaussZeroPointFourFourWithThreeHundredths :
    InternalFieldEstimate

record ZFMuSRTRSBEvidence : Set where
  constructor zfEvidence
  field
    normalSpectrum :
      Spectrum kelvinOnePointFive zeroApplied

    superconductingSpectrum :
      Spectrum kelvinZeroPointOne zeroApplied

    electronicRelaxationIncrease :
      RateIncrease lambdaNormal lambdaSuperconducting

    nuclearRelaxationStable :
      ApproximatelyEqualRate deltaNormal deltaSuperconducting

    lfSpectrum :
      Spectrum kelvinZeroPointOne longitudinalTenMilliTesla

    staticOrQuasistaticSupport :
      StaticDecouplingEvidence

    inferredInternalField :
      InternalFieldEstimate

open ZFMuSRTRSBEvidence public

paperMuSREvidence : ZFMuSRTRSBEvidence
paperMuSREvidence =
  zfEvidence
    zfNormal
    zfSuperconducting
    lambdaIncrease
    nuclearStable
    lfSuperconducting
    tenMilliTeslaDecouples
    gaussZeroPointFourFourWithThreeHundredths

-- Interpretation is intentionally a separate proposition.  The source
-- identifies the combined ZF/LF result as spontaneous TRS breaking; no
-- generic theorem "any magnetic field => superconducting TRSB" is added.
data SourceTRSBInterpretation : ZFMuSRTRSBEvidence → Set where
  katariaTRSBInterpretation :
    SourceTRSBInterpretation paperMuSREvidence

paperTRSBEvidence :
  SourceTRSBInterpretation paperMuSREvidence
paperTRSBEvidence = katariaTRSBInterpretation
