module DASHI.Physics.Closure.BothwellYe2022PublishedGradientPayloadExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.BothwellYe2022MillimetreRedshiftReceipt as Source

------------------------------------------------------------------------
-- Publication-level numeric payload for Bothwell et al. Nature 602 (2022).
--
-- This owner materialises only values printed in the public paper.  The
-- authors state that experimental data and analysis code are available from
-- the corresponding authors upon reasonable request; therefore raw arrays,
-- full covariance and code are deliberately not fabricated here.
------------------------------------------------------------------------

record PublishedGradientPayload : Set where
  field
    source : Source.BothwellYe2022Source
    sourceIsCanonical : source ≡ Source.canonicalBothwellYe2022Source

    gravityFormula : String
    laboratoryAcceleration : String
    predictedGradient : String
    weightedMeanGradient : String
    correctedGradient : String
    synchronousCorrectedGradient : String
    fractionalFrequencyUncertainty : String

    atomSpecies : String
    atomCount : String
    sampleGeometry : String
    imagingResolution : String
    effectivePixelSize : String
    latticeTilt : String
    campaignCount : String
    campaignDuration : String

    secondOrderZeemanGradientUncertainty : String
    dcStarkGradient : String
    blackBodyGradientUncertainty : String
    densityGradientUncertainty : String
    latticeLightGradientCorrection : String
    latticeLightGradientUncertainty : String

    publicRawDataAvailable : Bool
    publicRawDataAvailableIsFalse : publicRawDataAvailable ≡ false
    publicAnalysisCodeAvailable : Bool
    publicAnalysisCodeAvailableIsFalse : publicAnalysisCodeAvailable ≡ false
    availableFromCorrespondingAuthorsOnReasonableRequest : Bool
    availableFromCorrespondingAuthorsOnReasonableRequestIsTrue :
      availableFromCorrespondingAuthorsOnReasonableRequest ≡ true
    sourceArtifactSha256Present : Bool
    sourceArtifactSha256PresentIsFalse : sourceArtifactSha256Present ≡ false

    evidenceReading : List String

open PublishedGradientPayload public

canonicalPublishedGradientPayload : PublishedGradientPayload
canonicalPublishedGradientPayload = record
  { source = Source.canonicalBothwellYe2022Source
  ; sourceIsCanonical = refl
  ; gravityFormula = "delta f / f = a h / c^2"
  ; laboratoryAcceleration = "-9.796 m s^-2"
  ; predictedGradient = "-1.09e-19 mm^-1"
  ; weightedMeanGradient = "-1.00(12)e-19 mm^-1"
  ; correctedGradient = "-9.8(2.3)e-20 mm^-1"
  ; synchronousCorrectedGradient = "-1.28(27)e-19 mm^-1"
  ; fractionalFrequencyUncertainty = "7.6e-21"
  ; atomSpecies = "approximately 100000 ultracold 87Sr atoms"
  ; atomCount = "approximately 100000"
  ; sampleGeometry = "millimetre-scale sample in a vertically oriented 1D optical lattice"
  ; imagingResolution = "6 um class in-situ resolution"
  ; effectivePixelSize = "6.04 um"
  ; latticeTilt = "0.11(0.06) degrees"
  ; campaignCount = "14 gradient measurements"
  ; campaignDuration = "10 days; individual measurements 1 to 17 h"
  ; secondOrderZeemanGradientUncertainty = "4e-21 mm^-1"
  ; dcStarkGradient = "3(2)e-21 mm^-1"
  ; blackBodyGradientUncertainty = "3e-21 mm^-1"
  ; densityGradientUncertainty = "1.7e-20 mm^-1"
  ; latticeLightGradientCorrection = "-5e-21 mm^-1"
  ; latticeLightGradientUncertainty = "1e-21 mm^-1"
  ; publicRawDataAvailable = false
  ; publicRawDataAvailableIsFalse = refl
  ; publicAnalysisCodeAvailable = false
  ; publicAnalysisCodeAvailableIsFalse = refl
  ; availableFromCorrespondingAuthorsOnReasonableRequest = true
  ; availableFromCorrespondingAuthorsOnReasonableRequestIsTrue = refl
  ; sourceArtifactSha256Present = false
  ; sourceArtifactSha256PresentIsFalse = refl
  ; evidenceReading =
      "The public paper supplies the fitted and corrected gradient values, uncertainty, apparatus geometry and systematic-budget summary."
      ∷ "The public paper does not expose the underlying experimental arrays or analysis code; both are available from the corresponding authors on reasonable request."
      ∷ "No PDF checksum is manufactured by this owner; artifact SHA-256 remains an external acquisition obligation."
      ∷ []
  }

canonicalPublicRawDataUnavailable :
  publicRawDataAvailable canonicalPublishedGradientPayload ≡ false
canonicalPublicRawDataUnavailable = refl

canonicalPublishedNumericPayloadPresent : Bool
canonicalPublishedNumericPayloadPresent = true

canonicalPublishedNumericPayloadPresentIsTrue :
  canonicalPublishedNumericPayloadPresent ≡ true
canonicalPublishedNumericPayloadPresentIsTrue = refl
