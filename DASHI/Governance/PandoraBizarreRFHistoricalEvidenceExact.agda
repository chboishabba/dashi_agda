module DASHI.Governance.PandoraBizarreRFHistoricalEvidenceExact where

-- 2026-10-25: original-document source genealogy for the actual historical
-- intelligence-and-bioelectronics question raised by @itsgingertheory.
-- NOT a theorem of behavioral influence, a weapons-development claim, an
-- observation of a deployed human-targeting device, or a source of RF dosage.

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.InstitutionalAnomalousAlteredStateProgramAtlasExact as History

mkUltraOwner : History.ProgrammeFamily
mkUltraOwner = History.mkultraMksearchFamily

wiesner1964 : Source.AttributedSource
wiesner1964 = Source.mkNoDOISource
  "Jerome B. Wiesner, White House / President's Foreign Intelligence Advisory Board"
  "Bugging of the U.S. Embassy, Moscow"
  "Primary White House memorandum to Clark Clifford, 1964-06-24; National Security Archive document 28785"
  "1964"
  "https://nsarchive.gwu.edu/document/28785-document-1-white-house-jerome-wiesner-report-clark-clifford-bugging-us-embassy"
  Source.archivalSource
  "Inspected hidden listening equipment and recommended defensive wall-injected masking sound, acoustic security and electromagnetic reflection shielding; these were counter-surveillance proposals, not exposure treatments or demonstrated behavioural influence"
  Source.publicAttribution

mk119Memo : Source.AttributedSource
mk119Memo = Source.mkNoDOISource
  "CIA Technical Services Division / Research Branch (author redacted)"
  "MKULTRA Subproject 119, Draft Memorandum for the Record"
  "US government document dated 1960-08-17; grant approved 1960-09-09; Wikimedia mirror"
  "1960"
  "https://commons.wikimedia.org/wiki/File:MKUltra_119.pdf"
  Source.archivalSource
  "Funded annotated bibliography and survey; recording/analysis of biological electrical signals and remote electronic activation as research subjects; NOT proof of functional technology or experimental human activation. CIA CREST accession unresolved"
  Source.publicAttribution

cesaroPandora : Source.AttributedSource
cesaroPandora = Source.mkNoDOISource
  "Richard S. Cesaro, Advanced Research Projects Agency"
  "Justification Memorandum for Project PANDORA"
  "ARPA Project Plan 562, Top Secret memorandum; original scan via National Security Archive 28787"
  "1965"
  "https://nsarchive.gwu.edu/sites/default/files/documents/rhwvuj-tzy4b/03.pdf"
  Source.archivalSource
  "Established TUMS/ARPA/CIA/State multiagency administrative investigation and planned primate experiment, Air Force/APL/Walter Reed roles; NOT MK119 or a validated modern device"
  Source.publicAttribution

johnstonBizarre : Source.AttributedSource
johnstonBizarre = Source.mkNoDOISource
  "Joseph Johnston, CIA representative on Project PANDORA/BIZARRE"
  "Aid Memoir: Project BIZARRE results and their implications for TUMS"
  "CIA classified memo, 1967-09-25; National Security Archive original-object page 28791"
  "1967"
  "https://nsarchive.gwu.edu/document/28791-document-7-cia-memorandum-joseph-johnston-aid-memoir-sic-summary-statement-my"
  Source.archivalSource
  "One early animal behavioural claim at excessive initial signal estimate; follow-up at corrected dose negative; independent verification called for. Opinion about modulation is not a human mechanism proof"
  Source.publicAttribution


stateViralStudy1965 : Source.AttributedSource
stateViralStudy1965 = Source.mkNoDOISource
  "US Department of State, Medical Office"
  "Medical Services: Moscow Viral Study"
  "Secret cable 1965-12-09, National Security Archive item 28788"
  "1965"
  "https://nsarchive.gwu.edu/document/28788-document-4-department-state-medical-office-cable-medical-services-moscow-viral-study"
  Source.archivalSource
  "A misleading viral-study cover was proposed to obtain Moscow embassy employee/dependant blood for RF biological investigation; cable alone is not a clinical result"
  Source.publicAttribution

georgeWashington1966 : Source.AttributedSource
georgeWashington1966 = Source.mkNoDOISource
  "US Department of State, Medical Office"
  "Request for Contract - George Washington University"
  "1966-01-27, National Security Archive item 28789; Dr Cecil Jacobson, Human Cytogenetics Research Laboratory"
  "1966"
  "https://nsarchive.gwu.edu/document/28789-document-5-department-state-medical-office-memorandum-request-contract-george"
  Source.archivalSource
  "Describes an 11-month cytogenetic assay and classification of Moscow embassy blood samples, including separately planned animal confirmation; not a demonstrated radiation-health cause"
  Source.publicAttribution

pandoraApril1969 : Source.AttributedSource
pandoraApril1969 = Source.mkNoDOISource
  "ARPA PANDORA Science Advisory Committee; Lysle Peterson, Chair"
  "Summary and Detailed Minutes of 21 April 1969"
  "Meeting 1969-04-21, summary 1969-05-16; National Security Archive item 28794"
  "1969"
  "https://nsarchive.gwu.edu/document/28794-document-10-arpa-meeting-summaryminutes-summary-pandora-meeting-attached-detailed"
  Source.archivalSource
  "Executed Big Boy shipboard radar-exposure comparison: no significant group differences; GWU blood project reported 140 samples and four disputed chromosomal anomalies; further deliberate human irradiation remained prospective"
  Source.publicAttribution

pandoraHumanMinutes : Source.AttributedSource
pandoraHumanMinutes = Source.mkNoDOISource
  "ARPA PANDORA Science Advisory Committee"
  "Summary of Pandora Meeting with Detailed Minutes of April 21, 1969"
  "ARPA memorandum dated 1969-05-16; NSA Archive original-object page 28794"
  "1969"
  "https://nsarchive.gwu.edu/document/28794-document-10-arpa-meeting-summaryminutes-summary-pandora-meeting-attached-detailed"
  Source.archivalSource
  "Explicit discussion of prospective Fort Detrick human studies, blinding, concealment and shielding; planning does NOT establish subjects were exposed"
  Source.publicAttribution

koslovRand : Source.AttributedSource
koslovRand = Source.mkNoDOISource
  "Samuel Koslov, RAND Corporation"
  "Review of Project PANDORA Experiments"
  "RAND letter to Stephen Lukasik, 1969-11-04; original 5-page scan via National Security Archive 28796"
  "1969"
  "https://nsarchive.gwu.edu/sites/default/files/documents/rhwvuj-tzy4b/12.pdf"
  Source.archivalSource
  "Experiment-based negative/methodological review: primate results not convincing, EEG probe antenna artifact possible; separates possible weapon/interrogation inquiry from actual demonstrated response"
  Source.publicAttribution

senateMoscow1979 : Source.AttributedSource
senateMoscow1979 = Source.mkNoDOISource
  "United States Senate Committee on Commerce, Science, and Transportation"
  "Microwave Irradiation of the U.S. Embassy in Moscow: Review of Its History and Health Studies 1953–1977"
  "Committee print, April 1979; original scanned report mirrored by GWU National Security Archive document 15"
  "1979"
  "https://nsarchive.gwu.edu/sites/default/files/documents/rhwvuj-tzy4b/15.pdf"
  Source.governmentSource
  "Compiles State/GWU 1966–69 coded blood study and methodological negative reviews, PANDORA primate and Big Boy studies, lymphocyte cohort, and Johns Hopkins 1976–78 controlled-post observational epidemiology; no convincing detected causal effect at tested exposure levels, but cannot rule out later latent effects"
  Source.publicAttribution

hopkins1976To1978Study : Source.AttributedSource
hopkins1976To1978Study = Source.mkNoDOISource
  "Abraham Lilienfeld and team, Johns Hopkins University, for US State Department"
  "Foreign Service Health Status Study, compared Moscow and Eastern European posts"
  "Study conducted 1976–1978; 1979 US Senate committee print summarises methods/results; underlying investigator-level original data not retrieved"
  "1978"
  "https://nsarchive.gwu.edu/sites/default/files/documents/rhwvuj-tzy4b/15.pdf"
  Source.governmentSource
  "Measured morbidity/mortality retrospective comparison found no consistent dose-related excess; mortality follow-up relatively short and mixed symptom/disease differences acknowledged. This is not an independent new replication by the Senate"
  Source.publicAttribution

odniExperts : Source.AttributedSource
odniExperts = Source.mkNoDOISource
  "Office of the Director of National Intelligence, IC Experts Panel"
  "Executive Summary of the IC Experts Panel on Anomalous Health Incidents"
  "Declassified official expert-mechanism feasibility report dated 2022-02-01"
  "2022"
  "https://www.odni.gov/files/ODNI/documents/assessments/2022_02_01_AHI_Executive_Summary_FINAL_Redacted.pdf"
  Source.governmentSource
  "Pulsed RF plausible for certain AHI core features; ultrasound possible close access; distant sound/infrasound alone implausible for that feature set; panel did not attribute foreign actor"
  Source.publicAttribution

odni2025 : Source.AttributedSource
odni2025 = Source.mkNoDOISource
  "National Intelligence Council / ODNI"
  "Updated Assessment of Anomalous Health Incidents, as of December 2024"
  "ICA 2025-00008-B, publicly released 2025-01-10"
  "2025"
  "https://www.odni.gov/files/ODNI/documents/assessments/NIC-Unclassified-ICA-Updated-Assessment-AHI-December2024.pdf"
  Source.governmentSource
  "Five agencies strongly skeptical of an RF weapon; two minority analytic judgments about capability; no published incident-to-device operational attribution"
  Source.publicAttribution

recall2026 : Source.AttributedSource
recall2026 = Source.mkNoDOISource
  "Rick Crawford, Chair, House Permanent Select Committee on Intelligence (Majority)"
  "Statement on DNI recall of anomalous-health-incident intelligence assessments"
  "US House committee majority press release 2026-06-11"
  "2026"
  "https://intelligence.house.gov/2026/06/11/chairman-crawford-statement-on-director-gabbards-recall-of-the-flawed-intelligence-community-assessments-on-ahi/"
  Source.governmentSource
  "Political office states earlier ICAs were recalled; allegations of falsification are not independent findings and withdrawal is not a replacement specific-device scientific assessment"
  Source.publicAttribution

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Source.mkSourceAtlas
  "Cold War bioelectronic research and contemporary AHI original-object lineage"
  "DASHI.Governance.PandoraBizarreRFHistoricalEvidenceExact"
  (wiesner1964 ∷ mk119Memo ∷ cesaroPandora ∷ johnstonBizarre ∷ stateViralStudy1965 ∷
   georgeWashington1966 ∷ pandoraApril1969 ∷ pandoraHumanMinutes ∷
   koslovRand ∷ senateMoscow1979 ∷ hopkins1976To1978Study ∷
   odniExperts ∷ odni2025 ∷ recall2026 ∷ [])
  "Bounded original-document roots, no fabricated modern source-to-device bridge"

sourceAtlasNeverPromotes :
  GenericReceipt.promotesClaim
    (Source.attributedSourceAtlasReceipt sourceAtlas
      "No current same-actor apparatus or clinical exposure link is recovered")
  ≡ false
sourceAtlasNeverPromotes =
  Source.attributedSourceAtlasReceiptNonPromoting sourceAtlas
    "No current same-actor apparatus or clinical exposure link is recovered"

-- Named research objects. Topic similarity cannot be promoted to same project.
data ProgrammeObject : Set where
  mkUltraSubproject119 : ProgrammeObject
  arpaPandora : ProgrammeObject
  arpaBizarre : ProgrammeObject
  modernAnomalousHealthInquiry : ProgrammeObject
  stateMoscowViralStudy : ProgrammeObject
  navyBigBoy : ProgrammeObject
  moscowEmbassyCounterSurveillance : ProgrammeObject
  moscowEmbassyExposurePopulation : ProgrammeObject
  johnsHopkinsEmbassyFollowup : ProgrammeObject
  stateEmbassyLymphocyteSurvey : ProgrammeObject

data ProgrammeTopic : Set where bioelectronicsAndEffects : ProgrammeTopic

topic : ProgrammeObject → ProgrammeTopic
topic _ = bioelectronicsAndEffects

different1960And1965Objects :
  mkUltraSubproject119 ≡ arpaPandora → ⊥
different1960And1965Objects ()

-- Historical edge classes are NOT ordered by strength of evidence.
data LinkKind : Set where
  administrativeCoordination : LinkKind
  formalProgrammePart : LinkKind
  sourceDiscussesHypothesis : LinkKind
  sourceReportsExperiment : LinkKind
  criticalSameExperimentReview : LinkKind
  proposalOnly : LinkKind
  thematicNeighborOnly : LinkKind
  deploymentNotPaid : LinkKind
  documentedCoverStory : LinkKind
  fundedHumanObservation : LinkKind
  completedOccupationalComparison : LinkKind
  noControlledHumanIrradiationInThisRecord : LinkKind
  defensiveAudioCountermeasureProposal : LinkKind
  reportedMethodologicalRejection : LinkKind
  conductedComparativeEpidemiology : LinkKind
  observedHematologyWithoutDoseCorrelation : LinkKind

record BoundedLineageEdge : Set where
  constructor boundedLineageEdge
  field
    fromObject : ProgrammeObject
    toObject : ProgrammeObject
    edgeKind : LinkKind
    sourceObject : Source.AttributedSource
    sourceQualifiedRole : String
    withheldClaim : String

open BoundedLineageEdge public

pandoraBizarre : BoundedLineageEdge
pandoraBizarre = boundedLineageEdge
  arpaPandora arpaBizarre formalProgrammePart cesaroPandora
  "BIZARRE is a bounded primate-experiment component of PANDORA"
  "Subproject part does not prove efficacy, experimental safety or present-day deployment"

bizarreCritique : BoundedLineageEdge
bizarreCritique = boundedLineageEdge
  arpaBizarre arpaPandora criticalSameExperimentReview koslovRand
  "RAND 1969 independently reviewed the original PANDORA experiment data"
  "A negative critique is not proof there is no possible biological RF effect under any other conditions"

mk119PandoraAdjacentOnly : BoundedLineageEdge
mk119PandoraAdjacentOnly = boundedLineageEdge
  mkUltraSubproject119 arpaPandora thematicNeighborOnly mk119Memo
  "1960 funded bioelectric survey and 1965 RF biological experiment share a broad scientific theme"
  "No shared subject, apparatus, contract, director or programme-transfer source has been paid"

modernDeviceNotPaid : BoundedLineageEdge
modernDeviceNotPaid = boundedLineageEdge
  arpaBizarre modernAnomalousHealthInquiry deploymentNotPaid odni2025
  "A 2025 public analytic judgement considered possible foreign RF capability"
  "No verified declassified chain from 1960s apparatus to AHI device or contemporary commercial infrastructure"


wallMaskingAsDefensiveProposal : BoundedLineageEdge
wallMaskingAsDefensiveProposal = boundedLineageEdge
  moscowEmbassyCounterSurveillance moscowEmbassyCounterSurveillance
  defensiveAudioCountermeasureProposal wiesner1964
  "1964 White House memorandum proposes intentional masking sounds in walls to defeat embedded listening devices; no frequency or installed apparatus established, separate from tracking external RF beam"
  "No documented implementation or behavioural targeting; acoustic masking is a security countermeasure, not evidence of RF-to-acoustic mind control"

data MoscowSignalIntentHypothesis : Set where
  intendedNeurophysiologicalInfluence : MoscowSignalIntentHypothesis
  activateOrInterrogateImplantedListeningDevices : MoscowSignalIntentHypothesis
  jamOrConfuseRadioInterception : MoscowSignalIntentHypothesis
  otherOrUnknownIntent : MoscowSignalIntentHypothesis

-- Multiple contemporary hypotheses were investigated. This constructor
-- taxonomy cannot select which interpretation is actually true.

moscowCoverStory : BoundedLineageEdge
moscowCoverStory = boundedLineageEdge
  arpaPandora stateMoscowViralStudy documentedCoverStory stateViralStudy1965
  "US State Department staff used the Moscow Viral Study medical explanation to arrange observational blood collection"
  "Deceptive recruitment and biomarker analysis do not establish deliberate irradiation of participants or disease causation"

moscowCytogeneticContract : BoundedLineageEdge
moscowCytogeneticContract = boundedLineageEdge
  arpaPandora stateMoscowViralStudy fundedHumanObservation georgeWashington1966
  "Named 1966 11-month GWU laboratory assay contract and follow-on research; 1969 minutes subsequently report 140 examined blood samples"
  "Four reportedly abnormal chromosomes in historical minutes lack accepted causal identification"

navyBigBoyPerformed : BoundedLineageEdge
navyBigBoyPerformed = boundedLineageEdge
  arpaPandora navyBigBoy completedOccupationalComparison pandoraApril1969
  "USS Saratoga crew had actual psychological, physical, leucocyte and radar survey tests; no significant differences found"
  "Measured radar dose lower than predicted; negative study is not an absolute no-effect theorem"

humanExposurePlanNotExecutedByTheseMinutes : BoundedLineageEdge
humanExposurePlanNotExecutedByTheseMinutes = boundedLineageEdge
  arpaPandora arpaPandora noControlledHumanIrradiationInThisRecord pandoraApril1969
  "A future specially irradiated human group and blind controls were proposed in the 1969 minutes"
  "The record of proposed protocols is not a performed deliberate human exposure experiment"


moscowGWUPeerReviewNegative : BoundedLineageEdge
moscowGWUPeerReviewNegative = boundedLineageEdge
  stateMoscowViralStudy moscowEmbassyExposurePopulation
  reportedMethodologicalRejection senateMoscow1979
  "Final GWU sample series ca 250 specimens from >71 employees/family; independent reviews rejected biological causal inference and State declined renewal in June 1969"
  "The 1969 committee's earlier 140-sample report is a time-bounded intermediate observation, not a separate independent cohort"

hopkinsActualFollowup : BoundedLineageEdge
hopkinsActualFollowup = boundedLineageEdge
  moscowEmbassyExposurePopulation johnsHopkinsEmbassyFollowup
  conductedComparativeEpidemiology hopkins1976To1978Study
  "Actual 1976–78 controlled-post retrospective human outcome study, not a proposal; no convincing exposure-linked clinical effect detected in the population/time frame studied"
  "Cohort selection, medical ascertainment, dose uncertainty and late outcomes limit generality; no claim of RF impossibility or general public exposure safety"

lymphocyteNullDoseCorrelation : BoundedLineageEdge
lymphocyteNullDoseCorrelation = boundedLineageEdge
  moscowEmbassyExposurePopulation stateEmbassyLymphocyteSurvey
  observedHematologyWithoutDoseCorrelation senateMoscow1979
  "Survey measured higher mean lymphocyte counts in Moscow, without timing/location correlation to measured microwave irradiation; etiology unresolved"
  "Observed biomarker difference is not established RF-mediated disease or a proved alternative environmental cause"

data HumanStudyKind : Set where
  executedAmbientExposureObservation : HumanStudyKind
  executedBiologicalSampling : HumanStudyKind
  proposedControlledIrradiation : HumanStudyKind
  completedRetrospectiveEpidemiology : HumanStudyKind

retrospectiveComparativeOutcomeNotControlledIrradiation :
  completedRetrospectiveEpidemiology ≡ proposedControlledIrradiation → ⊥
retrospectiveComparativeOutcomeNotControlledIrradiation ()

sampledHumansAreNotProvenExperimentallyIrradiated :
  executedBiologicalSampling ≡ proposedControlledIrradiation → ⊥
sampledHumansAreNotProvenExperimentallyIrradiated ()

observedOccupationalExposureIsNotDeliberatelyAppliedProtocol :
  executedAmbientExposureObservation ≡ proposedControlledIrradiation → ⊥
observedOccupationalExposureIsNotDeliberatelyAppliedProtocol ()

-- Acoustic pressure oscillations, low-frequency modulation of microwave RF,
-- and EEG/biopotential measurements are separately typed observables.
data PhysicalCarrier : Set where
  airbornePressure : PhysicalCarrier
  microwaveRFCarrier : PhysicalCarrier
  biologicalElectricPotential : PhysicalCarrier

lowFrequencyModulatedRF : PhysicalCarrier
lowFrequencyModulatedRF = microwaveRFCarrier

industrialLowFrequencySound : PhysicalCarrier
industrialLowFrequencySound = airbornePressure

modulationDoesNotMakeAirSound :
  lowFrequencyModulatedRF ≡ industrialLowFrequencySound → ⊥
modulationDoesNotMakeAirSound ()
