module DASHI.Cognition.PsychotronicsScreenshotDiscriminationExact where

open import DASHI.Core.Prelude

import DASHI.Core.SnowballOSINTAcquisitionInvariantExact as OSINT
import DASHI.Physics.QuantumVacuum.DiscriminatingExperiment as Experiment
import DASHI.Cognition.PsychotronicsSuccorSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- CONCRETE CONSUMER: EIGHTEEN USER-SUPPLIED STILL SCREENSHOTS
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
  iPyramids : Creator
  aurumaya : Creator
  berndNindl : Creator
  officialPiggyPower : Creator
  moonaSmagicka : Creator
  theCitadel04 : Creator

data StillScene : Set where
  quartzTourmalineArc : StillScene
  crystalBenchEmitter : StillScene
  thermalReadout : StillScene
  curvedFreeAirArc : StillScene
  angularCopperCage : StillScene
  copperSphereInterior : StillScene
  torusCopperCrystalCase : StillScene
  torusAppInterface : StillScene
  succorHandheldQuartz : StillScene
  oudInAirDischarge : StillScene
  electrostaticMotorBench : StillScene
  waterVortexCarafe : StillScene
  speculativeBiopunkDiagram : StillScene

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

countStills : List ScreenshotEvidence → Nat
countStills [] = zero
countStills (_ ∷ frames) = suc (countStills frames)

stillAtlasHasTenFrames : countStills stillAtlas ≡ 10
stillAtlasHasTenFrames = refl

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


------------------------------------------------------------------------
-- SECOND USER ATTACHMENT BATCH: EIGHT NEW STILL SCREENSHOTS, 2026-10-24
-- Distinct native PNG SHA-256 values: these do not identify reel bytes.
-- Named product/poster or maker statements are *caption attestations*, not
-- independent validations of bio-effects or device measurements.
------------------------------------------------------------------------

waterSwirl : ScreenshotEvidence
waterSwirl = screenshot-evidence
  "1000018565.png"
  "86df9377c1af95d62c22868f9eb93772d9511ac4d3dd0a1013f51a8abdfc9c6e"
  moonaSmagicka waterVortexCarafe
  "Transparent vase-shaped water vortex device; copper triple-spiral ornament and coiled copper exterior"
  "On-screen search label MAYU Swirl structured water; Water is Magic claim"
  false false false false

oudinLoop : ScreenshotEvidence
oudinLoop = screenshot-evidence
  "1000018567.png"
  "7327aaf0a6ba02d4b6e5dd3d0257405b844fb7f8f832da1ea552757ceca55ce7"
  berndNindl oudInAirDischarge
  "Red copper loop around black surface; purple branching discharge visible below loop near fingertip"
  "Creator reply explicitly labels the device 'Oudin Oscillator'; user proximity is not a safety test"
  false false false false

oudinCoil : ScreenshotEvidence
oudinCoil = screenshot-evidence
  "1000018569.png"
  "6324ec164df5524fe117979d66351a04e16fafdd66400139030fff769a0ba1cc"
  berndNindl oudInAirDischarge
  "Large smooth metal sphere above a tall cylinder with many regularly repeating, pale serpentine horizontal bands; purple-blue luminous patches near upper bands, apparently on or near the winding; not enough detail to establish whether the pale bands are wires, reflections, insulation or another electrode"
  "Caption starts 'Triple insulated but directly you should not ...'; a separate post by this creator, not the same clip as the open-loop Oudin author reply; electrical topology and exact Oudin class NOT verified"
  false false false false

pignatelliCaptionedMotor : ScreenshotEvidence
pignatelliCaptionedMotor = screenshot-evidence
  "1000018571.png"
  "0a3ad0cf668c4165a090e548383380e7af6e313918ea9d3d5c45e6cc8959113f"
  officialPiggyPower electrostaticMotorBench
  "Parallel metallic bars between insulating-looking plates; leads and external power supply visible"
  "Caption identifies a Pignatelli motor and claims possible atmospheric-electricity drive; name/provenance unverified"
  false false false false

biopunkStory : ScreenshotEvidence
biopunkStory = screenshot-evidence
  "1000018572.png"
  "dc812dad48e04b9c78a5fbe8c5a6aa92569227238e9986d87a276d68ed56fdca"
  theCitadel04 speculativeBiopunkDiagram
  "Handwritten notebook with arrows, boxed labels, eyes and organic-body sketches"
  "Biopunk story concepts; presented as creative speculation rather than confirmed device mechanism"
  false false false false

itorusCase : ScreenshotEvidence
itorusCase = screenshot-evidence
  "1000018574.png"
  "e2d99e1d740db9212b788be64a471654dd038a69c403744cb811e5d3607a43ba"
  iPyramids torusCopperCrystalCase
  "Torus-shaped object with curved copper lattice/crystal elements in foam case next to electronics"
  "Creator names iTorus i9 pulsed EMF toroidal product"
  false false false false

itorusTablet : ScreenshotEvidence
itorusTablet = screenshot-evidence
  "1000018575.png"
  "22217e5322f736c1840496ed2c68c9ed2093081a2e9ab43721bdfabf9ca24cc6"
  iPyramids torusAppInterface
  "Tablet with iZen Meditation, Earth Based Therapy, Chakra Balance interface in front of toroid"
  "iTorus i9 bio-regeneration and room-sized coherent field marketing"
  false false false false

aurumayaSuccor : ScreenshotEvidence
aurumayaSuccor = screenshot-evidence
  "1000018577.png"
  "9d0cbf3a213c5139a1fcd7b2f655e6bf891ae9919a3f58fbad71bbff4562febb"
  aurumaya succorHandheldQuartz
  "Person holding translucent pointed quartz with coiled cable and small electronics"
  "Creator explicitly describes Succor Punch as Don Croft's device in a reply"
  false false false false

secondBatch : List ScreenshotEvidence
secondBatch = waterSwirl ∷ oudinLoop ∷ oudinCoil ∷
  pignatelliCaptionedMotor ∷ biopunkStory ∷
  itorusCase ∷ itorusTablet ∷ aurumayaSuccor ∷ []

secondBatchHasEight : countStills secondBatch ≡ 8
secondBatchHasEight = refl

bothBatchesHaveEighteen :
  (countStills stillAtlas + countStills secondBatch) ≡ 18
bothBatchesHaveEighteen = refl

data BrandStatementEstablishesMeasuredField : Set where
data HistoricDeviceNameEstablishesCurrentDeviceIdentity : Set where
data AtmosphericPotentialEstablishesMotorOutput : Set where
data WaterVortexEstablishesNewWaterPhase : Set where

noFieldFromMarketing : BrandStatementEstablishesMeasuredField → ⊥
noFieldFromMarketing ()

noSameObjectFromDeviceName : HistoricDeviceNameEstablishesCurrentDeviceIdentity → ⊥
noSameObjectFromDeviceName ()

noMotorPowerFromPotential : AtmosphericPotentialEstablishesMotorOutput → ⊥
noMotorPowerFromPotential ()

noWaterPhaseFromVortex : WaterVortexEstablishesNewWaterPhase → ⊥
noWaterPhaseFromVortex ()

------------------------------------------------------------------------
-- EXACT FIFTH IMAGE: IN THE USER'S EIGHT-SCREENSHOT DISPLAY ORDER.
-- This is a human-readable ordinal into the *presented sequence*, not a
-- carousel identity, chronological ordering, a new hardware identifier
-- or an inference from the internal secondBatch array ordering.
------------------------------------------------------------------------

displayOrder : List ScreenshotEvidence
displayOrder =
  itorusTablet ∷ aurumayaSuccor ∷ itorusCase ∷
  pignatelliCaptionedMotor ∷ oudinCoil ∷
  waterSwirl ∷ oudinLoop ∷ biopunkStory ∷ []

displayOrderEight : countStills displayOrder ≡ 8
displayOrderEight = refl

fifthImage : ScreenshotEvidence
fifthImage = oudinCoil

data TowerVisibleFeature : Set where
  smoothMetalSphere : TowerVisibleFeature
  verticalBody : TowerVisibleFeature
  paleSerpentineBands : TowerVisibleFeature
  violetPatchesNearUpperBands : TowerVisibleFeature

data TowerMechanismCandidate : Set where
  conventionalSphereTopRFResonator : TowerMechanismCandidate
  customSpacedSecondaryConductor : TowerMechanismCandidate
  surfaceOrInterTurnFlashover : TowerMechanismCandidate
  localCoronaFromElectrodeOrWinding : TowerMechanismCandidate
  imagingOrReflectionOfDischarge : TowerMechanismCandidate

record TowerDiscriminatorDemand : Set where
  constructor tower-discriminator-demand
  field
    candidate : TowerMechanismCandidate
    sourceReel : String
    wiringContinuity : String
    exposureAndFrameTiming : String
    locationOfVisibleDischarge : String
    powerSupplyIsolation : String
open TowerDiscriminatorDemand public

candidateTest : TowerMechanismCandidate → String
candidateTest conventionalSphereTopRFResonator =
  "native reel plus maker circuit, topload connection, winding/primary identification and calibrated electrical spectrum"
candidateTest customSpacedSecondaryConductor =
  "continuity/winding map and insulation description from builder, compared to native unobstructed stills"
candidateTest surfaceOrInterTurnFlashover =
  "non-contact supervised video locating arc endpoints with respect to successive turns and dielectric surfaces"
candidateTest localCoronaFromElectrodeOrWinding =
  "corona location and electrical field/voltage phase correlated with camera exposure under controlled safe setup"
candidateTest imagingOrReflectionOfDischarge =
  "second-view synchronised video and exposure/filter control to separate emitted light from reflection"

data FifthImageProvesOudinCircuit : Set where
data VisiblePurpleMeansTherapeuticField : Set where

fifthImageNeedsActualCircuit : FifthImageProvesOudinCircuit → ⊥
fifthImageNeedsActualCircuit ()

noClinicalInferenceFromPurple : VisiblePurpleMeansTherapeuticField → ⊥
noClinicalInferenceFromPurple ()
