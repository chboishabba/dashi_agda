module DASHI.Analysis.Maass.EisensteinCalibrationArtifact where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Analysis.MaassFourierCarrier as MFC
import DASHI.Analysis.Maass.ValidatedNumericsArtifact as VNA

------------------------------------------------------------------------
-- Known Eisenstein data calibrates the validated Fourier--Bessel pipeline.
-- It is explicitly a continuous-spectrum acceptance test and a cusp-form
-- rejection test: small automorphy/Laplace residuals alone cannot promote
-- this object to a cusp Maaß form.

record EisensteinCalibrationChecks : Set₁ where
  field
    cuspEnumerationChecked : Set
    constantTermExtractionChecked : Set
    scatteringConventionChecked : Set
    besselNormalizationChecked : Set
    laplacianSignChecked : Set
    generatorAutomorphyChecked : Set
    continuousSpectrumClassificationChecked : Set

record EisensteinCalibrationArtifact
  {Γ : MFC.ΓMaass}
  (state : MFC.TruncatedFourierState Γ)
  (Bytes Digest Payload EisensteinObject CertifiedContinuousSpectrumObject
    CuspMaassPromotion : Set)
  (isTheCalibratedEisenstein : EisensteinObject → Set)
  (continuousClassification : EisensteinObject → CertifiedContinuousSpectrumObject → Set)
  : Setω where
  field
    validatedNumerics : VNA.MaassValidatedNumericsArtifact state Bytes Digest Payload
    eisensteinObject : EisensteinObject
    objectIsEisenstein : isTheCalibratedEisenstein eisensteinObject

    acceptedContinuousObject : CertifiedContinuousSpectrumObject
    -- The checker, not a hand-set Boolean, must establish every calibration
    -- conclusion from the accepted frozen interval payload.
    calibrationCheckerSound :
      VNA.checker validatedNumerics (VNA.intervalPayload validatedNumerics) ≡
      true →
      EisensteinCalibrationChecks × continuousClassification eisensteinObject
        acceptedContinuousObject
    eisensteinCalibrationNotCusp : CuspMaassPromotion → ⊥

acceptedEisensteinCalibration :
  {Γ : MFC.ΓMaass} →
  {state : MFC.TruncatedFourierState Γ} →
  {Bytes Digest Payload EisensteinObject CertifiedContinuousSpectrumObject
    CuspMaassPromotion : Set} →
  {isTheCalibratedEisenstein : EisensteinObject → Set} →
  {continuousClassification : EisensteinObject → CertifiedContinuousSpectrumObject → Set} →
  (artifact : EisensteinCalibrationArtifact state Bytes Digest Payload EisensteinObject
    CertifiedContinuousSpectrumObject CuspMaassPromotion isTheCalibratedEisenstein
    continuousClassification) →
  EisensteinCalibrationChecks × continuousClassification
    (EisensteinCalibrationArtifact.eisensteinObject artifact)
    (EisensteinCalibrationArtifact.acceptedContinuousObject artifact)
acceptedEisensteinCalibration artifact =
  EisensteinCalibrationArtifact.calibrationCheckerSound artifact
    (VNA.checkerPassed (EisensteinCalibrationArtifact.validatedNumerics artifact))

open EisensteinCalibrationArtifact public
