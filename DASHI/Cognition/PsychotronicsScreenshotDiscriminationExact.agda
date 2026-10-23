module DASHI.Cognition.PsychotronicsScreenshotDiscriminationExact where

open import DASHI.Core.Prelude

import DASHI.Core.SnowballOSINTAcquisitionInvariantExact as OSINT
import DASHI.Physics.QuantumVacuum.DiscriminatingExperiment as Experiment
import DASHI.Cognition.PsychotronicsSuccorSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- CONCRETE CONSUMER: TEN USER-SUPPLIED STILL SCREENSHOTS
--
-- These are exact hashes of screenshot PNG attachments in the conversation,
-- not hashes of the original reels or the creator's originally uploaded
-- media. They are user-provided observations of public social-media posts.
-- Accounts, observed geometry, captions and inferred mechanisms are
-- retained separately. No still frame is a motion, voltage, spectrum,
-- instrument-calibration, video-authenticity or healing receipt.
------------------------------------------------------------------------

data Creator : Set where
  colourTheoryInstallations : Creator
  crystalPyramids96 : Creator

data StillScene : Set where
  quartzTourmalineArc : StillScene
  crystalBenchEmitter : StillScene
  thermalReadout : StillScene
  curvedFreeAirArc : StillScene
  angularCopperCage : StillScene
  copperSphereInterior : StillScene

record ScreenshotEvidence : Set where
  constructor screenshot-evidence
  field
    uploadedFilename : String
    sha256 : String
    creator : Creator
    scene : StillScene
    directlyVisible : String
    captionedClaim : String
    originalMediaURLInspected : Bool
    temporalMotionVerified : Bool
    instrumentCalibrationVerified : Bool
    electromagneticSpectrumMeasured : Bool
open ScreenshotEvidence public

-- The seven screenshots from @color_theory_installations are two or more
-- posts. Repeated stills are not independent corroboration.
quartzArcFirst : ScreenshotEvidence
quartzArcFirst = screenshot-evidence
  "1000018554.png"
  "87d11aae723c9d274b5d022424978061615fb6abb845e0c8c5bf6a7bcf74df4a"
  colourTheoryInstallations quartzTourmalineArc
  "Purple branching luminous discharge toward top of rough specimen"
  "Coherence engines and biofeedback; tourmaline/quartz from Myanmar"
  false false false false

quartzArc333 : ScreenshotEvidence
quartzArc333 = screenshot-evidence
  "1000018555.png"
  "c7304fe1a7e7bbc75593cb1e4268b079eedbb2e3dab0b85b07230c8e978ef625"
  colourTheoryInstallations quartzTourmalineArc
  "Purple branching discharge near green specimen and metal rod"
  "Schumann generator 7.83 Hz and alleged room-filling 333 Hz"
  false false false false

quartzArcClose : ScreenshotEvidence
quartzArcClose = screenshot-evidence
  "1000018557.png"
  "5d5e1fa0ad69c3bd6f6d6b9f1cb3dccf5d021b61aaf1b345c14cad5f52f3aeee"
  colourTheoryInstallations quartzTourmalineArc
  "Second still of violet discharge; no sequence or rotor axis verified"
  "333 Hz hashtag in post"
  false false false false

benchEmitter : ScreenshotEvidence
benchEmitter = screenshot-evidence
  "1000018558.png"
  "28bf021326c2bdb965843dd05781c9cd87c678573a361814d2fc8c1912d3d9cb"
  colourTheoryInstallations crystalBenchEmitter
  "Small blue circular-topped object with upward tip and violet glow near wire-wrapped crystals"
  "Gemstone oil exposed to device and astrological/eclipse language"
  false false false false

thermalScreen : ScreenshotEvidence
thermalScreen = screenshot-evidence
  "1000018559.png"
  "d2950548d64e4c677a6df659881444865755b6ce86e89d5653aeb1dfc6bc46fc"
  colourTheoryInstallations thermalReadout
  "Camera display labels Max 282.0 and a separate 69.2; units and emissivity not verified"
  "Energetic spike on piezoelectric quartz attributed to Tesla coil"
  false false false false

curvedArcComment : ScreenshotEvidence
curvedArcComment = screenshot-evidence
  "1000018560.png"
  "a929d0bf9b58bca0ee5f75f1dfa8479103cbf64c5d2717c0b922be4a1b66940b"
  colourTheoryInstallations curvedFreeAirArc
  "Curved violet branching electrical discharge in apparent open air above illuminated specimen"
  "Creator speculates about 7.83 Hz Schumann resonance interacting with Tesla coil"
  false false false false

curvedArcCaption : ScreenshotEvidence
curvedArcCaption = screenshot-evidence
  "1000018561.png"
  "5aeec01bceeb43f18a2b2ba1166c5ebe603ed6f1b1d5e024b1ae4dd48e6418e9"
  colourTheoryInstallations curvedFreeAirArc
  "Different still of curved discharge: luminous crescent and branching tips, not a verified independent orb"
  "UV candle quartz and fluorite description"
  false false false false

-- The three screenshots below are a DIFFERENT account and device family.
copperWide : ScreenshotEvidence
copperWide = screenshot-evidence
  "1000018562.png"
  "ed1e5f110cb35337aabdaf20d95f5d762f6d029b5cb6cf67f43c610b692f6935"
  crystalPyramids96 angularCopperCage
  "Angular overlapping copper strands and concentric/curved weave with small metal sphere"
  "PEMF biohacking and high-frequency matrix language"
  false false false false

copperMedium : ScreenshotEvidence
copperMedium = screenshot-evidence
  "1000018563.png"
  "f40ba8dd9297f2f6e8bab31a45cf0e977f932d907ab0af5f89fdc6e860867998"
  crystalPyramids96 copperSphereInterior
  "Metal sphere within copper basket/weave"
  "Changing timelines by changing personal vibrational rate"
  false false false false

copperClose : ScreenshotEvidence
copperClose = screenshot-evidence
  "1000018564.png"
  "5e69fb2da5580378fa6c0160eeaae9c34ab7ec7acb7008dc6b0b74dad8967526"
  crystalPyramids96 copperSphereInterior
  "Close still of reflective metal sphere near curved copper winding"
  "Commenter analogises small coil to CERN particle accelerators"
  false false false false

stillAtlas : List ScreenshotEvidence
stillAtlas =
  quartzArcFirst ∷ quartzArc333 ∷ quartzArcClose ∷
  benchEmitter ∷ thermalScreen ∷ curvedArcComment ∷
  curvedArcCaption ∷ copperWide ∷ copperMedium ∷
  copperClose ∷ []

stillAtlasCount : sourceCountPlaceholder ≡ sourceCountPlaceholder
stillAtlasCount = refl
  where
    sourceCountPlaceholder : Nat
    sourceCountPlaceholder = 10

-- OSINT acquisition and evidentiary admission are separate. The hashes
-- identify only screenshots; no social-media reel URL, original uploader
-- media byte sequence or driver calibration has been obtained.
screenshotOSINT : ScreenshotEvidence → OSINT.OSINTObservation
screenshotOSINT frame =
  OSINT.osint-observation
    (uploadedFilename frame)
    "original post and native reel URL unresolved"
    "2026-10-24 user-provided attachment"
    OSINT.archivedPublicArtifact
    OSINT.identityUnresolved
    (directlyVisible frame)
    "visible pixels / post overlay only; motion and meter data excluded"
    (sha256 frame)
    false
    true
    true

-- These are genuine competing hypotheses; *no* discriminator receipt is
-- inhabited. A planned control is a specification, never its own result.
data OpticalElectricalNull : Set where
  staticCoronaDischarge : OpticalElectricalNull
  mechanicalElectrodeRotation : OpticalElectricalNull
  ionWindElectrodeSpinner : OpticalElectricalNull
  phoneExposureAliasing : OpticalElectricalNull
  fluorescenceOrUVReflection : OpticalElectricalNull
  temperatureOrEmissivityArtefact : OpticalElectricalNull
  coupledOrModulatedWaveform : OpticalElectricalNull
  unmeasuredElectricalPickup : OpticalElectricalNull

controlNeeded : OpticalElectricalNull → String
controlNeeded staticCoronaDischarge =
  "lock electrode geometry; repeat as stationary reference with synced high-speed video"
controlNeeded mechanicalElectrodeRotation =
  "reference points on electrode; strobe and independent rotor-angle tracking"
controlNeeded ionWindElectrodeSpinner =
  "measure torque/angular response while varying geometry and airflow safely"
controlNeeded phoneExposureAliasing =
  "synchronise shutter timing to electrical waveform and independent high-speed camera"
controlNeeded fluorescenceOrUVReflection =
  "same illuminated sample with discharge switched off; filtered UV/visible spectra"
controlNeeded temperatureOrEmissivityArtefact =
  "matched emissivity, contact thermometry, thermal reference surfaces, same camera settings"
controlNeeded coupledOrModulatedWaveform =
  "simultaneous voltage/current and calibrated spectral recording; distinguish drive from modulation"
controlNeeded unmeasuredElectricalPickup =
  "shielded reference probe, known-pickup dummy conductor, baseline/no-drive acquisition"

record InstrumentedDeviceSignal : Set where
  constructor instrumented-device-signal
  field
    originalReelCustody : String
    driverAndElectrodeSameObject : String
    synchronisedMotionTrace : String
    voltageCurrentTrace : String
    spectrumWithUnits : String
    calibratedThermalTrace : String
    blindedControlAllocation : String
open InstrumentedDeviceSignal public

PhysicalDiscrimination : Set₁
PhysicalDiscrimination =
  Experiment.DiscriminatingExperiment InstrumentedDeviceSignal OpticalElectricalNull

ReplicatedPhysicalDiscrimination : Set₁
ReplicatedPhysicalDiscrimination =
  Experiment.ReplicatedDiscrimination InstrumentedDeviceSignal OpticalElectricalNull

-- Neither instrumented evidence nor null-exclusion receipts exist within this
-- file: a type declaration is an UNSATISFIED experiment requirement.
data StillImageProvesRotatingOrb : Set where
data ScreenshotTextProves333HzField : Set where
data ThermalDisplayProvesCrystalTemperature : Set where
data CroftWiringProvesInstagramDeviceIdentity : Set where

noMotionFromStill : StillImageProvesRotatingOrb → ⊥
noMotionFromStill ()

no333HzFieldFromOverlay : ScreenshotTextProves333HzField → ⊥
no333HzFieldFromOverlay ()

noCalibratedTemperatureFromScreen : ThermalDisplayProvesCrystalTemperature → ⊥
noCalibratedTemperatureFromScreen ()

noCroftIdentityFromAppearance : CroftWiringProvesInstagramDeviceIdentity → ⊥
noCroftIdentityFromAppearance ()

unpaidSourceAtlas : Atlas.Source.SourceKind
unpaidSourceAtlas = Atlas.Source.archivalSource
