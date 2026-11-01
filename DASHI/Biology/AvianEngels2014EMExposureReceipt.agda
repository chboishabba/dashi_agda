module DASHI.Biology.AvianEngels2014EMExposureReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AvianMagneticPerturbationSourceRegistry as Sources
import DASHI.Biology.AvianMagnetoreceptionEMExposureTransportExact as Exposure

------------------------------------------------------------------------
-- Source-bounded apparatus/calibration receipt for Engels et al. 2014.
--
-- Source scope retained here:
--   - European robins lost magnetic orientation under campus EM noise;
--   - grounded aluminium screening restored magnetic orientation;
--   - removing grounding or deliberately generating broadband EM noise
--     disrupted orientation again;
--   - birds at a rural location oriented without screening;
--   - electric and magnetic fields were measured;
--   - the experimental huts included a Merritt coil system.
--
-- No coil dimensions, drive settings, or operational animal protocol are
-- encoded here.  This is a provenance/calibration surface, not a procedure.
------------------------------------------------------------------------

data Engels2014Control : Set where
  unscreenedCampusNoise : Engels2014Control
  groundedAluminiumScreening : Engels2014Control
  ungroundedScreening : Engels2014Control
  generatedBroadbandNoise : Engels2014Control
  ruralBackground : Engels2014Control

data Engels2014Measurement : Set where
  electricFieldMeasurement : Engels2014Measurement
  magneticFieldMeasurement : Engels2014Measurement
  broadbandSpectrumMeasurement : Engels2014Measurement
  behavioralOrientationMeasurement : Engels2014Measurement

data Engels2014ApparatusBoundary : Set where
  merrittCoilNotPhasedArrayIdentity : Engels2014ApparatusBoundary
  screeningNotReceptorMechanismIdentity : Engels2014ApparatusBoundary
  measuredChamberFieldNotMicroscopicReceptorField : Engels2014ApparatusBoundary
  behavioralDisruptionNotUniqueMechanismProof : Engels2014ApparatusBoundary
  sourceReceiptNotOperationalProtocol : Engels2014ApparatusBoundary

canonicalEngelsControls : List Engels2014Control
canonicalEngelsControls =
  unscreenedCampusNoise
  ∷ groundedAluminiumScreening
  ∷ ungroundedScreening
  ∷ generatedBroadbandNoise
  ∷ ruralBackground
  ∷ []

canonicalEngelsMeasurements : List Engels2014Measurement
canonicalEngelsMeasurements =
  electricFieldMeasurement
  ∷ magneticFieldMeasurement
  ∷ broadbandSpectrumMeasurement
  ∷ behavioralOrientationMeasurement
  ∷ []

canonicalEngelsBoundaries : List Engels2014ApparatusBoundary
canonicalEngelsBoundaries =
  merrittCoilNotPhasedArrayIdentity
  ∷ screeningNotReceptorMechanismIdentity
  ∷ measuredChamberFieldNotMicroscopicReceptorField
  ∷ behavioralDisruptionNotUniqueMechanismProof
  ∷ sourceReceiptNotOperationalProtocol
  ∷ []

record Engels2014EMExposureReceipt : Set₁ where
  field
    source :
      Sources.AvianMagneticPerturbationSource

    sourceIsEngels2014 :
      source ≡ Sources.engelsEtAl2014

    genericExposureTransport :
      Exposure.AvianMagnetoreceptionEMExposureTransportReceipt

    controls :
      List Engels2014Control

    controlsAreCanonical :
      controls ≡ canonicalEngelsControls

    measurements :
      List Engels2014Measurement

    measurementsAreCanonical :
      measurements ≡ canonicalEngelsMeasurements

    boundaries :
      List Engels2014ApparatusBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalEngelsBoundaries

    groundedScreeningRestoresOrientation :
      Bool

    groundedScreeningRestoresOrientationIsTrue :
      groundedScreeningRestoresOrientation ≡ true

    removingGroundingDisruptsOrientation :
      Bool

    removingGroundingDisruptsOrientationIsTrue :
      removingGroundingDisruptsOrientation ≡ true

    generatedBroadbandNoiseDisruptsOrientation :
      Bool

    generatedBroadbandNoiseDisruptsOrientationIsTrue :
      generatedBroadbandNoiseDisruptsOrientation ≡ true

    ruralControlOrientsWithoutScreening :
      Bool

    ruralControlOrientsWithoutScreeningIsTrue :
      ruralControlOrientsWithoutScreening ≡ true

    electricAndMagneticFieldsMeasured :
      Bool

    electricAndMagneticFieldsMeasuredIsTrue :
      electricAndMagneticFieldsMeasured ≡ true

    merrittCoilSystemDocumented :
      Bool

    merrittCoilSystemDocumentedIsTrue :
      merrittCoilSystemDocumented ≡ true

    merrittCoilIsPhasedArray :
      Bool

    merrittCoilIsPhasedArrayIsFalse :
      merrittCoilIsPhasedArray ≡ false

    microscopicReceptorExposureRecovered :
      Bool

    microscopicReceptorExposureRecoveredIsFalse :
      microscopicReceptorExposureRecovered ≡ false

    receptorMechanismEstablished :
      Bool

    receptorMechanismEstablishedIsFalse :
      receptorMechanismEstablished ≡ false

    sourceReading :
      String

open Engels2014EMExposureReceipt public

canonicalEngels2014EMExposureReceipt : Engels2014EMExposureReceipt
canonicalEngels2014EMExposureReceipt =
  record
    { source = Sources.engelsEtAl2014
    ; sourceIsEngels2014 = refl
    ; genericExposureTransport =
        Exposure.canonicalAvianMagnetoreceptionEMExposureTransportReceipt
    ; controls = canonicalEngelsControls
    ; controlsAreCanonical = refl
    ; measurements = canonicalEngelsMeasurements
    ; measurementsAreCanonical = refl
    ; boundaries = canonicalEngelsBoundaries
    ; boundariesAreCanonical = refl
    ; groundedScreeningRestoresOrientation = true
    ; groundedScreeningRestoresOrientationIsTrue = refl
    ; removingGroundingDisruptsOrientation = true
    ; removingGroundingDisruptsOrientationIsTrue = refl
    ; generatedBroadbandNoiseDisruptsOrientation = true
    ; generatedBroadbandNoiseDisruptsOrientationIsTrue = refl
    ; ruralControlOrientsWithoutScreening = true
    ; ruralControlOrientsWithoutScreeningIsTrue = refl
    ; electricAndMagneticFieldsMeasured = true
    ; electricAndMagneticFieldsMeasuredIsTrue = refl
    ; merrittCoilSystemDocumented = true
    ; merrittCoilSystemDocumentedIsTrue = refl
    ; merrittCoilIsPhasedArray = false
    ; merrittCoilIsPhasedArrayIsFalse = refl
    ; microscopicReceptorExposureRecovered = false
    ; microscopicReceptorExposureRecoveredIsFalse = refl
    ; receptorMechanismEstablished = false
    ; receptorMechanismEstablishedIsFalse = refl
    ; sourceReading =
        "Engels et al. 2014 supplies source-bounded control and field-measurement receipts for EM-noise disruption of robin magnetic orientation; exact microscopic receptor exposure and receptor identity remain unresolved."
    }
