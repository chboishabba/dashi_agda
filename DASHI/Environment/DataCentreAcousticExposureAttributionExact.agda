module DASHI.Environment.DataCentreAcousticExposureAttributionExact where

-- Data-centre acoustic evidence boundary, 2026-10-24.
-- Distinguishes source output, calibrated measurement, receptor exposure,
-- outcome association and causal interpretation. This module does NOT assert
-- that any observed data-centre exposure produces a particular disease.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Planning.DataCentreUrbanResourceConflictExact as Planning
import DASHI.Biology.AvianMagnetoreceptionEMExposureTransportExact as EM

data PhysicalChannel : Set where
  airbornePressure : PhysicalChannel
  structureBorneMotion : PhysicalChannel
  electricMagneticField : PhysicalChannel
  atmosphericEmission : PhysicalChannel

data EvidenceStage : Set where
  creatorClaimOnly : EvidenceStage
  methodologicalReview : EvidenceStage
  proceduralStandard : EvidenceStage
  facilityActivity : EvidenceStage
  calibratedSourceEmission : EvidenceStage
  ambientMeasurement : EvidenceStage
  attributableReceptorExposure : EvidenceStage
  modelledHealthImpact : EvidenceStage
  observedOutcome : EvidenceStage
  identifiedCausalEffect : EvidenceStage

data AuthorityClass : Set where
  primaryInstrumentData : AuthorityClass
  practitionerPublishedFieldFigure : AuthorityClass
  peerReviewedExperimental : AuthorityClass
  peerReviewedReview : AuthorityClass
  creatorInvestigation : AuthorityClass
  communityTestimony : AuthorityClass
  advocacyInterpretation : AuthorityClass
  regulatorOrPlanningInstrument : AuthorityClass

record SourceBoundClaim : Set where
  constructor sourceBoundClaim
  field
    sourceTitle : String
    sourceURI : String
    sourceClass : AuthorityClass
    sourceStage : EvidenceStage
    supportedScope : String
    withheldPromotion : String

gingerReel : SourceBoundClaim
gingerReel = sourceBoundClaim
  "itsgingertheory: Frequency is only the tip of the data center..."
  "https://www.instagram.com/reel/DbqY4jLxuhs/"
  creatorInvestigation creatorClaimOnly
  "Creator statements and on-screen bibliography photographed 2026-10-24"
  "Displayed review, commercial article, advocacy quotation or animal study does not establish the spoken human causal chain"

bennJordanDocumentary : SourceBoundClaim
bennJordanDocumentary = sourceBoundClaim
  "Benn Jordan: Datacenters Behaving Like Acoustic Weapons (2026-02-18)"
  "https://www.youtube.com/watch?v=_bP80DEAbuo"
  creatorInvestigation ambientMeasurement
  "Field investigation, community reporting and exploratory short-exposure comparison"
  "Absolute calibrated receptor dose, masked analyses and published causal replication not yet recovered"

wheelerNarrativeReview : SourceBoundClaim
wheelerNarrativeReview = sourceBoundClaim
  "Wheeler, Everett, Williamson, Prybutok (2026): ILFN Data Center Environments"
  "https://doi.org/10.3390/cleantechnol8040126"
  peerReviewedReview methodologicalReview
  "A-weighted metrics discount low frequencies; operational ILFN spectrum and human outcome research gaps"
  "Review analogy does not itself measure site exposure or prove illness"

environmentEvidenceMap : SourceBoundClaim
environmentEvidenceMap = sourceBoundClaim
  "Environmental Pressures and Modelled Health Pathways of Data Centers in the AI Era (2026)"
  "https://doi.org/10.3390/environments13100568"
  peerReviewedReview methodologicalReview
  "36 included studies and 112 quantitative estimates; none reaches directly observed health outcome"
  "Absence in this eligible evidence map is not proof of zero risk"

-- ORIGINAL PRACTITIONER FIELD SOURCE, newer than Aug 2026 reviews:
-- David Woolworth, Roland Woolworth & Associates, Noise/News
-- International, 9 Sep 2026, original Figures 1-3 visually inspected.
-- This is original published on-site spectral graphics, not a
-- peer-reviewed health study or publicly archived raw WAV/binary series.
woolworth2026OriginalFieldFigures : SourceBoundClaim
woolworth2026OriginalFieldFigures = sourceBoundClaim
  "David Woolworth (Roland, Woolworth & Associates) 2026: Data centers and measurement of low frequency and infrasound, original Figures 1-3"
  "https://noisenewsinternational.net/data-centers-and-measurement-of-low-frequency-and-infrasound/"
  practitionerPublishedFieldFigure ambientMeasurement
  "Original Sep 9 2026 practitioner-reported field spectral graphics of cooling tower cases including Scaife Rd and anonymized Data Center X (Fig 1), power-plant/turbine receiving levels (Fig 2), and site wind-contaminated low-frequency spectrogram (Fig 3). Fig 1 dBA/dBC pairs: Scaife 64/74; Center X 70/78, 70/78, 70/80; chart axes 6.3 to 10000 Hz. Author explicitly says no significant infrasound in Fig 1 cooling tower samples but does find low-frequency tones and envelope pulsing."
  "No numeric waveform bins or unprocessed native recordings, full receiver calibration, exact industrial activity/time joins, independently replicated site exposure, person outcome or human disease result in the published article. Anonymized Data Center X traces are not three independent source locations. Wind-polluted spectrogram (Fig 3) is at natural-gas plant, not an identified data-center sensor. Do not treat 2026 earlier review saying no published DC ILFN study as evergreen after later original evidence."

-- A real published plot is a documentary primary measurement summary.
-- It pays ORIGINAL FIELD FIGURE availability but cannot stand in for
-- authentic raw site-time samples or an identified health effect.
data DataCentreFieldEvidenceStanding : Set where
  authorPublishedIndustrialSpectrumFigure : DataCentreFieldEvidenceStanding
  originalCalibratedWaveformAndResponse : DataCentreFieldEvidenceStanding
  loadMatchedAmbientReceiverAttribution : DataCentreFieldEvidenceStanding
  siteMatchedObservedClinicalOutcome : DataCentreFieldEvidenceStanding

figureIsNotRawWaveform :
  authorPublishedIndustrialSpectrumFigure ≡
    originalCalibratedWaveformAndResponse → ⊥
figureIsNotRawWaveform ()

figureDoesNotVerifySourceCausality :
  authorPublishedIndustrialSpectrumFigure ≡
    loadMatchedAmbientReceiverAttribution → ⊥
figureDoesNotVerifySourceCausality ()

figureDoesNotVerifyHumanOutcome :
  authorPublishedIndustrialSpectrumFigure ≡
    siteMatchedObservedClinicalOutcome → ⊥
figureDoesNotVerifyHumanOutcome ()

data PublishedSoundMetric : Set where
  nominalFrequencyWeightedLevelA : PublishedSoundMetric
  nominalFrequencyWeightedLevelC : PublishedSoundMetric
  calibratedNativeSub20HzSpectrum : PublishedSoundMetric

weightedCNotInfrasoundAmplitude :
  nominalFrequencyWeightedLevelC ≡
    calibratedNativeSub20HzSpectrum → ⊥
weightedCNotInfrasoundAmplitude ()

-- Attribution-first original *human* infrasound experimental roots.
-- The 2021, 2023 and 2026 experiments target different signals, exposures,
-- durations and outcomes. They are three original-study roots, not three
-- replications of Benn Jordan or a particular data-centre community.
-- A distinct SOURCE-ORIGINAL actual human infrasound perceptual lab,
-- not human environmental disease or a DC site-measured source signal:
-- Jurado, Marquardt Sci Rep 16 19097, original Apr 24 2026,
-- article version-of-record Jun 19 2026, original DOI preserved.
juradoMarquardt2026Cochlea : SourceBoundClaim
juradoMarquardt2026Cochlea = sourceBoundClaim
  "Carlos Jurado and Torsten Marquardt (2026): Infrasound sensation is mediated by intracochlear electrical potentials"
  "https://doi.org/10.1038/s41598-026-50179-w"
  peerReviewedExperimental observedOutcome
  "Original non-invasive human audiology/psychophysics: threshold shifts for 4 8 and 16 Hz under added high-frequency masking, plus OAE/sensation results; authors report masker threshold shifts 5.5, 5.8, 3.2 dB at 4 8 16 Hz with tests T(6). A cochlear lumped-circuit model proposes OHC-driven electrical potentials can contribute to auditory nerve sensation without conventional IHC velocity-driven excitation at very low Hz."
  "Perception at sufficient tested ear-canal stimulus is NOT absence of audibility, but NOT proof of chronic disease, subclinical hormonal injury, environmental data-centre source-receptor pressure or specific intentional RF programme. Model excitation mechanism is a supported interpretation, not directly recorded voltage in these volunteers; original study reports raw data/scripts available on reasonable request, not direct in-repo assets."

scattertyControlled2026 : SourceBoundClaim
scattertyControlled2026 = sourceBoundClaim
  "Scatterty, VonStein, Prichard, Franczak, Hamilton, Schmaltz (2026): infrasound, affect and cortisol"
  "https://doi.org/10.3389/fnbeh.2026.1729876"
  peerReviewedExperimental observedOutcome
  "Randomized 2x2 laboratory experiment July-August 2023, published 2026: 36 initially randomized, 35 retained cortisol/PANAS records; ~18 Hz 75-78 dB for 4m40s; multiple self-report effects and pre/post cortisol measured. Original supplemental participant CSV DOI 10.3389/fnbeh.2026.1729876.s002."
  "The reported W=192, p=0.022 is recovered from n=35 whole sample, not the n=18 infrasound-on subgroup; original study and independent segyges reproduction distinct roots. This does NOT establish a facility receptor health effect or chronic disease. Covariate-adjusted models and numerous post-exposure item tests require bounded sensitivity analysis."

maijala2021WindExperiment : SourceBoundClaim
maijala2021WindExperiment = sourceBoundClaim
  "Maijala, Kurki, Vainio, Pakarinen, Kuuramo et al. (2021): original wind-turbine infrasound experiment"
  "https://doi.org/10.1121/10.0003509"
  peerReviewedExperimental observedOutcome
  "Original field-selected wind turbine sound samples and controlled lab provocation; participants did not identify infrasonic content and the specific tested exposure showed no independent annoyance/heart-rate/skin-conductance effect"
  "A null result for its specific wind-turbine spectrum, dose and endpoints is not a universal null for other frequencies, levels or source locations."

marshall2023WindCrossover : SourceBoundClaim
marshall2023WindCrossover = sourceBoundClaim
  "Marshall, Cho, Toelle, Tonin et al. (2023): 72h double-blind wind turbine infrasound crossover"
  "https://doi.org/10.1289/EHP10757"
  peerReviewedExperimental observedOutcome
  "Original randomized sham/traffic-active-control laboratory experiment, 37 randomized noise-sensitive adults, 1.6-20 Hz ~90 dB peak across 72h; primary wake-after-sleep-onset mean contrast -1.36 min 95 percent CI -6.60 to 3.88; traffic active-control contrast +6.07 min"
  "Within-study null at tested dose and sleep/physiological endpoints does not refute all human infrasound effects and is not a real data-centre community exposure trial."

-- A recognized original physiological measurement in a controlled lab
-- never becomes the *same object* as an in-situ industrial source-receptor
-- human-outcome join. The whole-sample before/after test is also not an
-- infrasound-group randomized contrast. Distinct nonidentities are source
-- audit gates rather than a medical or causal theorem.
data HumanAcousticEvidenceRoot : Set where
  originalHumanInfrasoundCochlearSensationLab : HumanAcousticEvidenceRoot
  originalShortLabRandomizedAffectCortisol : HumanAcousticEvidenceRoot
  originalWindTurbineAnnoyanceLab : HumanAcousticEvidenceRoot
  originalLongShamCrossoverSleepLab : HumanAcousticEvidenceRoot
  actualDataCentreMatchedReceptorOutcome : HumanAcousticEvidenceRoot

cochlearPerceptionNotClinicalDataCentreCase :
  originalHumanInfrasoundCochlearSensationLab ≡
    actualDataCentreMatchedReceptorOutcome → ⊥
cochlearPerceptionNotClinicalDataCentreCase ()

shortLabIsNotDataCentreReceptor :
  originalShortLabRandomizedAffectCortisol ≡
    actualDataCentreMatchedReceptorOutcome → ⊥
shortLabIsNotDataCentreReceptor ()

windStudyIsNotDataCentreReceptor :
  originalLongShamCrossoverSleepLab ≡
    actualDataCentreMatchedReceptorOutcome → ⊥
windStudyIsNotDataCentreReceptor ()

data CortisolContrastRole : Set where
  allParticipantPrePostSignedRanks : CortisolContrastRole
  onConditionOnlyPrePostSignedRanks : CortisolContrastRole
  betweenRandomizedOnOffChangeContrast : CortisolContrastRole

allSamplePrePostNotOnOnly :
  allParticipantPrePostSignedRanks ≡
    onConditionOnlyPrePostSignedRanks → ⊥
allSamplePrePostNotOnOnly ()

allSampleBeforeAfterNotRandomizedExposureContrast :
  allParticipantPrePostSignedRanks ≡
    betweenRandomizedOnOffChangeContrast → ⊥
allSampleBeforeAfterNotRandomizedExposureContrast ()

queenslandNoisePolicy : SourceBoundClaim
queenslandNoisePolicy = sourceBoundClaim
  "Queensland Environmental Protection (Noise) Policy 2019"
  "https://www.legislation.qld.gov.au/view/whole/html/2026-01-28/sl-2019-0154"
  regulatorOrPlanningInstrument proceduralStandard
  "Acoustic environmental values, receptor objectives, sleep and amenity"
  "A statutory objective does not itself establish a concrete site compliant or noncompliant"

data PhysicalClaimCategory : Set where
  acousticNoiseClaim : PhysicalClaimCategory
  rfBiologicalClaim : PhysicalClaimCategory

claimChannel : PhysicalClaimCategory → PhysicalChannel
claimChannel acousticNoiseClaim = airbornePressure
claimChannel rfBiologicalClaim = electricMagneticField

data HistoricalClaimCategory : Set where
  intelligenceHistoryClaim : HistoricalClaimCategory

-- Historical documentary records are not a physical measurement channel.
-- Neither the existence of ARTICHOKE nor a contemporary RF carrier
-- identifies a common device, waveform, subject or operation.

-- Minimal *linear weighted-power proxy*, not a dB(A) meter.
-- Positive toy weights 2 and 3 stand for two different band sensitivities.
-- Different band distributions (3,0) and (0,2) yield the same scalar 6.
-- The actual logarithmic, frequency-weighted LAeq has the same many-to-one
-- identifiability issue, but this toy is not its physical calibration.
data TwoBandSpectrum : Set where
  lowOnly : TwoBandSpectrum
  highOnly : TwoBandSpectrum

weightedPowerProxy : TwoBandSpectrum → Nat
weightedPowerProxy lowOnly = 2 * 3 + 3 * 0
weightedPowerProxy highOnly = 2 * 0 + 3 * 2

sameWeightedProxy :
  weightedPowerProxy lowOnly ≡ weightedPowerProxy highOnly
sameWeightedProxy = refl

spectraRemainDifferent : lowOnly ≡ highOnly → ⊥
spectraRemainDifferent ()

-- Woolworth Fig 1 reports both dBA and dBC for source plots.
-- TWO scalar summaries still do not determine a frequency-resolved
-- 3-or-more-band physical spectrum. This is a fully exact *toy power*
-- witness, not calibrated ANSI/IEC dB(A) or dB(C) and never a 20-Hz
-- measurement. It refutes the general inverse-map uniqueness shortcut.
data ThreeBandSpectrum : Set where
  firstThreeBandProfile : ThreeBandSpectrum
  secondThreeBandProfile : ThreeBandSpectrum

firstToyWeightedProxy : ThreeBandSpectrum → Nat
firstToyWeightedProxy firstThreeBandProfile =
  1 * 5 + 2 * 5 + 1 * 5
firstToyWeightedProxy secondThreeBandProfile =
  1 * 4 + 2 * 4 + 1 * 8

secondToyWeightedProxy : ThreeBandSpectrum → Nat
secondToyWeightedProxy firstThreeBandProfile =
  2 * 5 + 1 * 5 + 1 * 5
secondToyWeightedProxy secondThreeBandProfile =
  2 * 4 + 1 * 4 + 1 * 8

sameTwoWeightedBandProxies :
  firstToyWeightedProxy firstThreeBandProfile ≡
    firstToyWeightedProxy secondThreeBandProfile
sameTwoWeightedBandProxies = refl

sameSecondWeightedBandProxy :
  secondToyWeightedProxy firstThreeBandProfile ≡
    secondToyWeightedProxy secondThreeBandProfile
sameSecondWeightedBandProxy = refl

differentThreeBandProfiles :
  firstThreeBandProfile ≡ secondThreeBandProfile → ⊥
differentThreeBandProfiles ()

record EvidenceGate : Set where
  constructor evidenceGate
  field
    hasTimeStampedCalibratedSPL : Bool
    hasTraceableDeviceCalibration : Bool
    hasNoiseFloorAndWindAudit : Bool
    hasFrequencyResolvedPressureSpectrum : Bool
    hasIndependentVibrationMeasurement : Bool
    hasReceptorSpatialTransfer : Bool
    hasOperationalOnOffComparison : Bool
    hasPrespecifiedConfounderControl : Bool
    hasReproducedHealthOutcome : Bool
    hasSpecificRFOrOtherCouplingProof : Bool

-- Default: conservative UNKNOWN represented as "not paid", not physical false.
defaultUnpaid : EvidenceGate
defaultUnpaid =
  evidenceGate false false false false false false false false false false

planningOwner : Planning.Project
planningOwner = Planning.aiDataCentre

emTransportOwner : EM.EMExposureTransportSurface
emTransportOwner = EM.canonicalEMExposureTransportSurface

data RoadmapPhase : Set where
  bibliographyRecovered : RoadmapPhase
  dimensionalModelComplete : RoadmapPhase
  calibratedSiteMeasurementsNeeded : RoadmapPhase
  sourceToReceptorValidationNeeded : RoadmapPhase
  causalHealthStudyNeeded : RoadmapPhase
  policyApplicationNeedsSiteRecord : RoadmapPhase

currentPhases : List RoadmapPhase
currentPhases =
  bibliographyRecovered ∷ dimensionalModelComplete ∷
  calibratedSiteMeasurementsNeeded ∷ sourceToReceptorValidationNeeded ∷
  causalHealthStudyNeeded ∷ policyApplicationNeedsSiteRecord ∷ []

-- Formal non-identifiability witness is exact for the toy carrier.
-- It is NOT an external-world claim, a source-identification algorithm,
-- an Agda proof of human health harm, or a validated FEM/acoustic solver.
