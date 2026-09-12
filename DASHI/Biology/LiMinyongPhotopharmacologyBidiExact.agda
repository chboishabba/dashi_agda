module DASHI.Biology.LiMinyongPhotopharmacologyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificCapabilityCarrierBidiExact as C
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T

------------------------------------------------------------------------
-- LI MINYONG: PHOTOPHARMACOLOGY / FLUORESCENT MOLECULAR PROBES
--
-- Source coordinates:
--   DOI 10.1002/med.22120 (2025 photopharmacology review)
--   CN201110101082.5 and CN201110100874.0 (probe patent coordinates)
--
-- This owner types the reversible light-control / molecular-readout chain.
-- Exact wavelengths, compounds, affinities and in-vivo efficacy remain tied to
-- the selected source object and are not invented here.
------------------------------------------------------------------------

data PhotoControlStage : Set where
  photonInput photoswitchStateChange targetEncounter targetBinding
  molecularOrPhysiologicalReadout recoveryOrReverseSwitch : PhotoControlStage

record PhotoControlModel : Set where
  constructor photo-control-model
  field
    sourceReferences : String
    molecularFamily : String
    stages : List PhotoControlStage
    intendedMechanism : String
    missingExecutableCoordinate : String

open PhotoControlModel public

canonicalLiMinyongPhotoControlModel : PhotoControlModel
canonicalLiMinyongPhotoControlModel = photo-control-model
  "DOI 10.1002/med.22120; CN201110101082.5; CN201110100874.0"
  "azobenzene-based photopharmacology and fluorescent receptor/target probes"
  (photonInput ∷ photoswitchStateChange ∷ targetEncounter ∷ targetBinding ∷
   molecularOrPhysiologicalReadout ∷ recoveryOrReverseSwitch ∷ [])
  "use light-dependent molecular state changes or fluorescent probes to control or observe target-specific biological interactions"
  "select one exact compound/probe and recover wavelength bands, isomer/state fractions, affinity/selectivity, dose, fluorescence or physiological readout and reversibility kinetics"

liMinyongCarrier : C.ScientificCapabilityCarrier
liMinyongCarrier = C.scientific-capability-carrier
  "medicinal chemistry / molecular imaging"
  "photoswitch/probe constitutive and response parameters"
  C.constitutiveParameters
  C.carrierPublic
  "light-dependent state change, target binding and optical/physiological readout"
  "DOI 10.1002/med.22120; probe patent coordinates"
  "Review/patent objects expose mechanism families and examples; exact compound performance and experimental state are source-specific."

liMinyongTransformation : T.ApplicationTransformation
liMinyongTransformation = T.application-transformation
  "photopharmacology and molecular visualisation"
  (T.governingPhysics ∷ T.constitutiveConfiguration ∷ [])
  (T.operatingWindow ∷ T.calibrationState ∷ T.validationCorpus ∷
   T.uncertaintyModel ∷ T.qualificationEvidence ∷ [])
  "Li Minyong review/patent science"
  "Application requires source-specific wavelengths, dose/concentration, target context, optical calibration and biological validation."

data LiMinyongReverseTarget : Set where
  selectExactCompound acquireWavelengthBands acquirePhotostationaryState
  acquireBindingAffinity acquireSelectivity acquireDoseWindow acquireReadoutCalibration
  acquireReversibilityKinetics acquireInVivoValidation acquireLabCustodian : LiMinyongReverseTarget

probeOrReviewImpliesClinicalEfficacy : Bool
probeOrReviewImpliesClinicalEfficacy = false

photoswitchMechanismImpliesAnyTargetControllable : Bool
photoswitchMechanismImpliesAnyTargetControllable = false

photoControlCanSupportTargetedResearchAssays : Bool
photoControlCanSupportTargetedResearchAssays = true
