module DASHI.Analysis.Maass.EisensteinCalibrationArtifact where

open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)

import DASHI.Analysis.MaassFourierCarrier as MFC
import DASHI.Analysis.Maass.ValidatedNumericsArtifact as VNA

------------------------------------------------------------------------
-- Known Eisenstein data calibrates the validated Fourier--Bessel pipeline.
-- It is explicitly a continuous-spectrum acceptance test and a cusp-form
-- rejection test: small automorphy/Laplace residuals alone cannot promote
-- this object to a cusp Maaß form.

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

    -- These are checker-facing calibration obligations.  A concrete producer
    -- must make them consequences of its accepted interval payload.
    cuspEnumerationChecked : Set
    constantTermExtractionChecked : Set
    scatteringConventionChecked : Set
    besselNormalizationChecked : Set
    laplacianSignChecked : Set
    generatorAutomorphyChecked : Set
    continuousSpectrumClassificationChecked : Set

    acceptedContinuousObject : CertifiedContinuousSpectrumObject
    acceptedAsContinuous : continuousClassification eisensteinObject
      acceptedContinuousObject
    eisensteinCalibrationNotCusp : CuspMaassPromotion → ⊥

open EisensteinCalibrationArtifact public
