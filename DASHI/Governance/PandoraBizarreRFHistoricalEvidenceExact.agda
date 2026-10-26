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

byronOperational1966 : Source.AttributedSource
byronOperational1966 = Source.mkNoDOISource
  "Eugene V. Byron, Johns Hopkins University Applied Physics Laboratory"
  "Operational Procedure for Project Pandora Microwave Test Facility (MRT-4-045/QM-66-071)"
  "Original institutional report dated October 1966; DoD FOIA release is indexed but direct PDF access blocked at retrieval"
  "1966"
  "https://www.esd.whs.mil/Portals/54/Documents/FOID/Reading%20Room/Other/Operational_Procedure_For_Project_Pandora.pdf"
  Source.archivalSource
  "Original equipment/control/field-monitor report identity verified from indexed scan excerpts; full pages not independently obtained. Apparatus documentation is not animal physiology or a modern operational technology transfer"
  Source.publicAttribution

byronFinal1966 : Source.AttributedSource
byronFinal1966 = Source.mkNoDOISource
  "Eugene V. Byron, Johns Hopkins University Applied Physics Laboratory"
  "Project Pandora (U), Final Report (MRT-4-046/QM-66-072)"
  "Original instrument and chamber evaluation dated November 1966; contained in same DoD FOIA assembly as Operational Procedure"
  "1966"
  "https://www.esd.whs.mil/Portals/54/Documents/FOID/Reading%20Room/Other/Operational_Procedure_For_Project_Pandora.pdf"
  Source.archivalSource
  "Indexed original report discusses field nonuniformity, probe geometry and sample container reflections. Third-party indexed snippets, not full-page independently inspected; neither an in-vivo effect nor effective weapon result"
  Source.publicAttribution

arpaInitial1966 : Source.AttributedSource
arpaInitial1966 = Source.mkNoDOISource
  "Richard S. Cesaro / Advanced Research Projects Agency"
  "Project PANDORA - Initial Test Results, Memorandum for Record"
  "20 December 1966, citing original 15 Dec 1966 test report; text reproduced in secondary scans while official archival original awaits direct reinspection"
  "1966"
  "https://www.acalltoactions.com/_files/ugd/905ae8_0f91de6cd63343a5929e231def551d99.pdf"
  Source.archivalSource
  "Preliminary single-primate high-dose modulated RF performance slowdown report; physiological CNS-penetration assertion is author's interpretation, not direct brain recording. Reproduction does not establish independent repetition or clinical efficacy"
  Source.publicAttribution

cesaroSeptember1967 : Source.AttributedSource
cesaroSeptember1967 = Source.mkNoDOISource
  "Richard S. Cesaro, Advanced Research Projects Agency"
  "Project BIZARRE - Memorandum for Director, Defense Research and Engineering"
  "27 September 1967, three-page declassified scan, National Security Archive object 28792"
  "1967"
  "https://nsarchive.gwu.edu/sites/default/files/documents/rhwvuj-tzy4b/08.pdf"
  Source.archivalSource
  "Original scan personally inspected: reported high-dose modulated primate performance decrement; same-level unmodulated controls normal; <=0.05 mW/cm2 corrected Moscow signal and lower-dose primate null. Reference 2 says 20 December 1967 (future date) where separate original is reproduced as 20 December 1966; retain discrepancy"
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

lilienfeld1978Original : Source.AttributedSource
lilienfeld1978Original = Source.mkNoDOISource
  "Abraham M. Lilienfeld; J. Tonascia; S. Tonascia; C. H. Libauer; G. M. Cauthen"
  "Evaluation of Health Status of Foreign Service and Other Employees from Selected Eastern European Posts"
  "Johns Hopkins University School of Hygiene and Public Health for US State Department, final report 1978, NTIS accession PB288163, government NTRL original record; 447 pages"
  "1978"
  "https://ntrl.ntis.gov/NTRL/dashboard/searchResults/titleDetail/PB288163.xhtml"
  Source.archivalSource
  "Original investigator human retrospective study: US NTIS lists 1827 Moscow employees/dependants and 2561 other Eastern European embassy comparators; original report available in public mirrored PDF, but full tables and individual matched dose methods not independently audited this round. Report authors conclude no adverse RF health effects shown in the studied cohort; disputed endpoint interpretation remains recorded by 2012 independent review"
  Source.publicAttribution

mallalieu1980PhysicalModel : Source.AttributedSource
mallalieu1980PhysicalModel = Source.mkNoDOISource
  "Robert C. Mallalieu, Johns Hopkins University Applied Physics Laboratory"
  "A Model of the Microwave Intensity Distribution within the U.S. Embassy in Moscow, 1966–1977"
  "Original APL report FS-80-166, August 1980; 81 pages and 53 references indexed in DOE/ER-0098; reprinted as section C of NTIA-SP-81-12"
  "1980"
  "https://www.gbppr.net/mil/havana/pb83155804.pdf"
  Source.archivalSource
  "Retrospective field reconstruction using validated dated and situated probe readings, geometry, reflections, antenna/probe verification, distinct 1966–1975 TUMS and 1975–1977 MUTS systems, building shielding and screened windows; text indexed but full source PDF not rendered from this access carrier"
  Source.publicAttribution

ntia1981Assessment : Source.AttributedSource
ntia1981Assessment = Source.mkNoDOISource
  "US National Telecommunications and Information Administration; Electromagnetic Radiation Management Advisory Council; US Department of State; Johns Hopkins Applied Physics Laboratory"
  "Microwave Radiation at the U.S. Embassy in Moscow and Its Biological Implications: An Assessment"
  "1981 US Department of Commerce original special publication NTIA-SP-81-12; Government Publishing Office catalogue item C 60.9:81-12; official NTIA Institute for Telecommunication Sciences index"
  "1981"
  "https://its.ntia.gov/publications/search-results"
  Source.governmentSource
  "Original official composite publication: repeats 1980 Mallalieu physical field model, State personnel assignment exposure model, and original 26 Aug 1980 ERMAC expert low-level health-risk assessment. Assembled source is not three independent replicated cohorts; ERMAC concluded harmful effects not anticipated at modelled particular levels. Full official PDF not directly rendered here"
  Source.publicAttribution

elwood2012Review : Source.AttributedSource
elwood2012Review = Source.mkDOISource
  "J. Mark Elwood"
  "Microwaves in the cold war: the Moscow embassy study and its interpretation. Review of a retrospective cohort study"
  "Environmental Health 11, article 85"
  "2012"
  "10.1186/1476-069X-11-85"
  "https://doi.org/10.1186/1476-069X-11-85"
  Source.academicArticleSource
  "Original independently authored 2012 scholarly critical re-analysis of the 1978 investigator report; supports authors' no consistent demonstrated adverse exposure-effect association within cohort limitations. NOT a fresh or blinded independent human cohort replication"
  Source.publicAttribution

kubisDecember1969 : Source.AttributedSource
kubisDecember1969 = Source.mkNoDOISource
  "Joseph F. Kubis, PANDORA Scientific Advisory Committee"
  "On Evaluation of Data Associated with Pandora (Preliminary Report)"
  "Original 1969-12-04 committee methodological evaluation, indexed as pages 283–299 of DoD FOIA Pandora records bundle; full page images not examined here"
  "1969"
  "https://www.esd.whs.mil/Portals/54/Documents/FOID/Reading%20Room/Other/Operational_Procedure_For_Project_Pandora.pdf"
  Source.archivalSource
  "Same animal programme retrospective methodological assessment: treatment of baseline, experimental/control contamination and cumulative-effect assumptions disputed; original text index not an independent new primate experiment"
  Source.publicAttribution

pandoraCommitteeJanuary1970 : Source.AttributedSource
pandoraCommitteeJanuary1970 = Source.mkNoDOISource
  "Lysle H. Peterson, PANDORA Scientific Advisory Committee, Institute for Defense Analyses"
  "Minutes of the Pandora Meeting of January 12, 1970"
  "1970-01-12 meeting; summary typed 1970-03-23, original indexed DoD FOIA Pandora bundle, page-label 1–6; full official scan access denied"
  "1970"
  "https://www.esd.whs.mil/Portals/54/Documents/FOID/Reading%20Room/Other/Operational_Procedure_For_Project_Pandora.pdf"
  Source.archivalSource
  "Committee judged WRAIR special-signal primate performance studies negative for a clear and strong effect and said further human controlled tests likely similarly inconclusive; explicitly warned that lab signal reproduced only components of original Moscow signal. No general RF no-effect claim"
  Source.publicAttribution

pandoraErratumMarch1970 : Source.AttributedSource
pandoraErratumMarch1970 = Source.mkNoDOISource
  "Chanda, secretary to Herbert Pollack, Institute for Defense Analyses"
  "Letter correcting a double negative in the January 12 Pandora Committee summary"
  "Original dated 1970-03-31 correction letter to Richard S. Cesaro, indexed with original DoD FOIA PANDORA bundle; image not independently inspected"
  "1970"
  "https://www.esd.whs.mil/Portals/54/Documents/FOID/Reading%20Room/Other/Operational_Procedure_For_Project_Pandora.pdf"
  Source.archivalSource
  "Editorial correction changes committee's double-negative wording about absence of expected permanent deleterious effects; restores original intended safety sentence, but not proof of safe exposure. The erratum edits the existing January source root, not a new experiment"
  Source.publicAttribution

koslovNavyZaret1971 : Source.AttributedSource
koslovNavyZaret1971 = Source.mkNoDOISource
  "Samuel Koslov et al., RAND technical review panel for US Navy"
  "Review of Contract N00014-69-C-0358 Radio Frequency Hazards, investigator Milton M. Zaret"
  "1971-08-16 RAND panel report, original US National Archives RG46, National Security Archive item 28797; government original report, distinct contract from WRAIR main trial"
  "1971"
  "https://nsarchive.gwu.edu/document/28797-document-13-rand-corporation-samuel-koslov-et-al-report-assistant-secretary-navy-rd"
  Source.archivalSource
  "Original 1971 RAND panel separately evaluated (1) Hawaii Zaret Foundation primate RF/cataract study, judged scientifically invalid with missing exposure logging, untested metallic restraint perturbations and three of five deaths attributed to strangulation, and (2) Polytechnic Institute of Brooklyn 2450 MHz rabbit heat/respiration/temperature investigation judged adequately conducted. Same Navy contract, distinct sites/protocols; no RF-caused deaths demonstrated"
  Source.publicAttribution

heilmeier1977 : Source.AttributedSource
heilmeier1977 = Source.mkNoDOISource
  "George H. Heilmeier, Director, Defense Advanced Research Projects Agency"
  "Letter to Senator Warren G. Magnuson concerning Project Pandora"
  "Primary signed two-page ARPA letter, 1977-09-15, National Security Archive document 28798; physically inspected both pages"
  "1977"
  "https://nsarchive.gwu.edu/sites/default/files/documents/rhwvuj-tzy4b/14.pdf"
  Source.archivalSource
  "1977 agency-accounting assertion: total $4,615,000, DARPA held only technical progress reports and minutes, raw records amassed by original researchers, unknown raw-record disposition; March 1970 programme terminated and equipment assets transferred to WRAIR for disposition. Statement disclaiming mind-control-project awareness must be read next to 1967 discussion of possible future weapons research: interpretive tension, not proved false oath or functional technology"
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
  (wiesner1964 ∷ mk119Memo ∷ cesaroPandora ∷
   byronOperational1966 ∷ byronFinal1966 ∷ arpaInitial1966 ∷
   cesaroSeptember1967 ∷ johnstonBizarre ∷ stateViralStudy1965 ∷
   georgeWashington1966 ∷ pandoraApril1969 ∷ pandoraHumanMinutes ∷
   koslovRand ∷ kubisDecember1969 ∷ pandoraCommitteeJanuary1970 ∷
   pandoraErratumMarch1970 ∷ koslovNavyZaret1971 ∷ heilmeier1977 ∷ lilienfeld1978Original ∷
   mallalieu1980PhysicalModel ∷ ntia1981Assessment ∷
   senateMoscow1979 ∷ hopkins1976To1978Study ∷ elwood2012Review ∷
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
  walterReedMicrowaveTestFacility : ProgrammeObject
  originalPrimateHighDoseExperiment : ProgrammeObject
  correctedLowDoseReplication : ProgrammeObject
  tumsEmbassyFieldMeasurements : ProgrammeObject
  pandoraResearchersRawRecords : ProgrammeObject
  darpaProgressAndMinutes : ProgrammeObject
  wrairFacilityAssetsDisposition : ProgrammeObject
  wrairPlannedExpandedFacility1969 : ProgrammeObject
  darpa1977DisavowalStatement : ProgrammeObject
  pandoraMcIlwainExperimentalReassessment : ProgrammeObject
  pandora1970CommitteeFinalReassessment : ProgrammeObject
  navyZaretSeparateExposureContract : ProgrammeObject
  mallalieuRetrospectivePhysicalFieldModel : ProgrammeObject
  ntia1981CompiledAssessment : ProgrammeObject
  lilienfeldCompleted1978HumanReport : ProgrammeObject
  laterScientificReviewOfSameCohort : ProgrammeObject

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
  originalApparatusEngineeringReport : LinkKind
  sourceReportedPreliminaryOutcome : LinkKind
  subsequentDoseReassessment : LinkKind
  sourceReferenceChronologyConflict : LinkKind
  originalResearcherRecordCustodyStatement : LinkKind
  agencyProgressOnlyStatement : LinkKind
  historicalEquipmentDispositionTransfer : LinkKind
  expansionFacilityUnderConstructionReport : LinkKind
  disputedRetrospectiveCharacterisation : LinkKind
  contemporaryExperimentalReassessment : LinkKind
  originalExperimentalEnvironmentalConfound : LinkKind
  reconstructedHistoricalExposureField : LinkKind
  priorStudyAnalyzedWithFollowupModel : LinkKind
  originalHumanInvestigatorReport : LinkKind
  expertReassessmentOfReusedFieldAndCohort : LinkKind
  independentReviewerSameCohort : LinkKind
  committeeOriginalStudyReassessment : LinkKind
  signedCorrectiveErratum : LinkKind
  separateContractCriticalReview : LinkKind

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

mallalieuReconstructedField : BoundedLineageEdge
mallalieuReconstructedField = boundedLineageEdge
  tumsEmbassyFieldMeasurements mallalieuRetrospectivePhysicalFieldModel
  reconstructedHistoricalExposureField mallalieu1980PhysicalModel
  "Mallalieu 1980 reconstructs physical field by source era and room/window/reflection/antenna geometry using validated historical measurements"
  "A retrospective model is not the missing original CIA 13 Sep 1967 instrument time series and no individual person's measured absorbed dose is supplied"

lilienfeldPerformedHealthReport : BoundedLineageEdge
lilienfeldPerformedHealthReport = boundedLineageEdge
  moscowEmbassyExposurePopulation lilienfeldCompleted1978HumanReport
  originalHumanInvestigatorReport lilienfeld1978Original
  "US government NTIS accession PB288163 identifies the original completed investigator study, authors and Moscow 1827 vs comparator 2561 subjects; no extra cohort inferred from 1979 Senate review"
  "Finding of no observed adverse association is study-conditional; neither a proof of universal human RF safety nor of industrial sound exposure"

ntiaCompositeReusesModel : BoundedLineageEdge
ntiaCompositeReusesModel = boundedLineageEdge
  mallalieuRetrospectivePhysicalFieldModel ntia1981CompiledAssessment
  expertReassessmentOfReusedFieldAndCohort ntia1981Assessment
  "NTIA publication packages independently authored original retrospective physical field model, State location exposure assignment and 1980 ERMAC expert judgement"
  "Cannot count reprinting Mallalieu results as independent field measurement; ERMAC assessment does not create a newly observed clinical intervention"

elwoodUsesSame1978Cohort : BoundedLineageEdge
elwoodUsesSame1978Cohort = boundedLineageEdge
  lilienfeldCompleted1978HumanReport laterScientificReviewOfSameCohort
  independentReviewerSameCohort elwood2012Review
  "Elwood 2012 independently evaluates original 1978 Lilienfeld study's methods and alternative interpretations"
  "Independently authored review does not create new patient-year outcomes, new exposure groups or causal proof"

data HistoricalStudyIdentity : Set where
  original1978Cohort : HistoricalStudyIdentity
  secondary1979ReportOfSameCohort : HistoricalStudyIdentity
  retrospective2012ReviewOfSameCohort : HistoricalStudyIdentity

-- Different publication objects, but ALL use the same underlying 1978
-- retrospective cohort, so they do not become three independent samples.
data ExperimentReplicationRole : Set where
  genuinelyNewHumanCohort : ExperimentReplicationRole
  interpretationOfExistingCohort : ExperimentReplicationRole

reviewIsNotNewCohort :
  interpretationOfExistingCohort ≡ genuinelyNewHumanCohort → ⊥
reviewIsNotNewCohort ()

-- Three separate publication objects do NOT imply three independently
-- recruited populations. This is a finite Ibrahim source-root regression.
data HistoricalCohortPublication : Set where
  lilienfeld1978InvestigatorReport : HistoricalCohortPublication
  senate1979Retelling : HistoricalCohortPublication
  elwood2012IndependentReview : HistoricalCohortPublication

data CohortSourceRoot : Set where
  lilienfeldOriginalPopulation : CohortSourceRoot

cohortSourceRoot : HistoricalCohortPublication → CohortSourceRoot
cohortSourceRoot lilienfeld1978InvestigatorReport = lilienfeldOriginalPopulation
cohortSourceRoot senate1979Retelling = lilienfeldOriginalPopulation
cohortSourceRoot elwood2012IndependentReview = lilienfeldOriginalPopulation

senateReportIsNotNewPopulation :
  cohortSourceRoot lilienfeld1978InvestigatorReport ≡
  cohortSourceRoot senate1979Retelling
senateReportIsNotNewPopulation = refl

elwoodReviewIsNotNewPopulation :
  cohortSourceRoot lilienfeld1978InvestigatorReport ≡
  cohortSourceRoot elwood2012IndependentReview
elwoodReviewIsNotNewPopulation = refl

-- Field reconstruction and an observed prospective source run have different
-- empirical authority. The actual 1967 probe measurements are NOT replaced
-- by a 1980 retrospective fitted spatiotemporal physical map.
data RFFieldEvidenceObject : Set where
  original1967SensorReading : RFFieldEvidenceObject
  mallalieu1980RetrospectiveModel : RFFieldEvidenceObject
  ntia1981SameModelReprint : RFFieldEvidenceObject

data FieldEvidenceStanding : Set where
  firsthandInstrumentTrace : FieldEvidenceStanding
  reconstructedModel : FieldEvidenceStanding
  reproducedModel : FieldEvidenceStanding

fieldStanding : RFFieldEvidenceObject → FieldEvidenceStanding
fieldStanding original1967SensorReading = firsthandInstrumentTrace
fieldStanding mallalieu1980RetrospectiveModel = reconstructedModel
fieldStanding ntia1981SameModelReprint = reproducedModel

modelIsNotOriginalSensorRecord :
  fieldStanding mallalieu1980RetrospectiveModel ≡
  fieldStanding original1967SensorReading → ⊥
modelIsNotOriginalSensorRecord ()

-- Different signal / shielding eras are NOT automatically comparable:
-- 1980 Mallalieu reports separately TUMS, later MUTS-1/2, and 1976
-- screen installation. These constructors are documentary categories only.
data MoscowRFExposureEra : Set where
  tums1966ToMay1975 : MoscowRFExposureEra
  mutsMay1975ToFeb1976 : MoscowRFExposureEra
  mutsScreenedAfterFeb1976 : MoscowRFExposureEra

eraIsNotInterchangeable :
  tums1966ToMay1975 ≡ mutsScreenedAfterFeb1976 → ⊥
eraIsNotInterchangeable ()

pandoraFinalCommitteeAssessment : BoundedLineageEdge
pandoraFinalCommitteeAssessment = boundedLineageEdge
  pandoraMcIlwainExperimentalReassessment pandora1970CommitteeFinalReassessment
  committeeOriginalStudyReassessment pandoraCommitteeJanuary1970
  "January 1970 committee, typed March 23, synthesised Kubis and McIlwain reanalysis and judged performed WRAIR laboratory animal effects negative for clear, strong behavioural change"
  "WRAIR reproduced selected Moscow wave components only; cannot extend result to every original complex waveform, human body or other observed outcome"

pandoraErratumCorrectsOneDocument : BoundedLineageEdge
pandoraErratumCorrectsOneDocument = boundedLineageEdge
  pandora1970CommitteeFinalReassessment pandora1970CommitteeFinalReassessment
  signedCorrectiveErratum pandoraErratumMarch1970
  "31 March 1970 IDA secretary correction of double negative in committee safety sentence; same scientific committee source/document"
  "Corrected committee risk language is not calibrated long-term no-harm proof and its separate carrier is not a new empirical observation"

navyZaretCriticalSeparateContract : BoundedLineageEdge
navyZaretCriticalSeparateContract = boundedLineageEdge
  arpaBizarre navyZaretSeparateExposureContract separateContractCriticalReview koslovNavyZaret1971
  "1971 Koslov et al. Navy N00014-69-C-0358 review rejected the Lualualei/Pearl Harbor primate exposure experiment for field/animal failures but explicitly assessed Brooklyn's separate rabbit 2450 MHz laboratory work as adequately controlled"
  "Related historical RF research is not automatically the same animals, laboratory, grant or direct RF-caused mortality"

data NavyZaretContractSite : Set where
  hawaiiPrimateStudy : NavyZaretContractSite
  brooklynRabbitStudy : NavyZaretContractSite

data Navy1971MethodologicalVerdict : Set where
  invalidPrimateMeasurements : Navy1971MethodologicalVerdict
  adequateRabbitMeasurements : Navy1971MethodologicalVerdict

reviewVerdict : NavyZaretContractSite → Navy1971MethodologicalVerdict
reviewVerdict hawaiiPrimateStudy = invalidPrimateMeasurements
reviewVerdict brooklynRabbitStudy = adequateRabbitMeasurements

separateNavySubstudiesNotEqual :
  hawaiiPrimateStudy ≡ brooklynRabbitStudy → ⊥
separateNavySubstudiesNotEqual ()

differentSubstudyMethodologyVerdicts :
  reviewVerdict hawaiiPrimateStudy ≡ reviewVerdict brooklynRabbitStudy → ⊥
differentSubstudyMethodologyVerdicts ()

data ScientificEvidenceRole : Set where
  retrospectiveCommitteeReassessment : ScientificEvidenceRole
  originalIndividualExperimentalRuns : ScientificEvidenceRole
  separateNavyContractReview : ScientificEvidenceRole

committeeSynthesisIsNotRawTrial :
  retrospectiveCommitteeReassessment ≡ originalIndividualExperimentalRuns → ⊥
committeeSynthesisIsNotRawTrial ()

navyContractIsNotWrairRawTrial :
  separateNavyContractReview ≡ originalIndividualExperimentalRuns → ⊥
navyContractIsNotWrairRawTrial ()

data CommitteeSourceCarrier : Set where
  originalJanuaryMinutes : CommitteeSourceCarrier
  correctionMarchLetter : CommitteeSourceCarrier

data OriginalCommitteeRoot : Set where
  committeeJanuary1970StudyRoot : OriginalCommitteeRoot

committeeRoot : CommitteeSourceCarrier → OriginalCommitteeRoot
committeeRoot _ = committeeJanuary1970StudyRoot

erratumDoesNotCreateIndependentStudy :
  committeeRoot originalJanuaryMinutes ≡ committeeRoot correctionMarchLetter
erratumDoesNotCreateIndependentStudy = refl

pandoraKoslovObservedOriginalRecords : BoundedLineageEdge
pandoraKoslovObservedOriginalRecords = boundedLineageEdge
  originalPrimateHighDoseExperiment pandoraMcIlwainExperimentalReassessment
  contemporaryExperimentalReassessment koslovRand
  "Koslov's 4 Nov 1969 letter identifies Major James T McIlwain as presenter of original PANDORA animal records, including four operantly conditioned animals, seven special-signal exposures, two square, one triangular and one continuous-wave control; these counts are Koslov's recollection, not newly recovered per-animal source data"
  "Koslov considered behavioural changes nonspecific and EEG results possibly artifacts; his 8-hour review is NOT original raw participant-by-trial experiment receipts or independent replication"

pandoraBigBoyNoiseAsRecordedConfound : BoundedLineageEdge
pandoraBigBoyNoiseAsRecordedConfound = boundedLineageEdge
  navyBigBoy arpaPandora originalExperimentalEnvironmentalConfound pandoraApril1969
  "April 21 1969 detailed meeting minutes explicitly report high ship noise, PA interruptions in the quiet testing room and unstable line voltage during Saratoga human observational assessments"
  "Environmental acoustic noise as a confound does NOT prove a sound-and-RF biological interaction or establish any RF-related medical outcome"

data ExperimentOrInstrumentRecord : Set where
  originalRawAnimalTrialTrace : ExperimentOrInstrumentRecord
  reviewerSummaryOfAnimalTraces : ExperimentOrInstrumentRecord
  custodialEquipmentInventory : ExperimentOrInstrumentRecord

reviewIsNotRawParticipantData :
  reviewerSummaryOfAnimalTraces ≡ originalRawAnimalTrialTrace → ⊥
reviewIsNotRawParticipantData ()

assetInventoryIsNotExperimentTrace :
  custodialEquipmentInventory ≡ originalRawAnimalTrialTrace → ⊥
assetInventoryIsNotExperimentTrace ()

pandoraRecordsOriginalResearcherCustody : BoundedLineageEdge
pandoraRecordsOriginalResearcherCustody = boundedLineageEdge
  arpaPandora pandoraResearchersRawRecords originalResearcherRecordCustodyStatement heilmeier1977
  "In his 15 Sep 1977 signed response DARPA director Heilmeier said original researchers amassed the raw data; the agency did not know what disposition was made"
  "Does NOT establish raw data survived or went with equipment to WRAIR; actual researcher archive and retention schedule remain unknown"

pandoraAgencyProgressNotRaw : BoundedLineageEdge
pandoraAgencyProgressNotRaw = boundedLineageEdge
  arpaPandora darpaProgressAndMinutes agencyProgressOnlyStatement heilmeier1977
  "DARPA says it received technical progress reports and had declassified Pandora minutes and technical reports"
  "Its original source-claim is a statement by 1977 DARPA, not an authenticated exhaustive researcher files inventory"

pandoraAssetsTransferredToWRAIR : BoundedLineageEdge
pandoraAssetsTransferredToWRAIR = boundedLineageEdge
  arpaPandora wrairFacilityAssetsDisposition historicalEquipmentDispositionTransfer heilmeier1977
  "Heilmeier reports that on closure March 1970 all Pandora programme assets transferred to Walter Reed Army Institute of Research for disposition"
  "Assets do not mean raw experimental data and transfer for disposition does not mean the equipment remained operational"

pandoraFacilityExpansionProposed1969 : BoundedLineageEdge
pandoraFacilityExpansionProposed1969 = boundedLineageEdge
  walterReedMicrowaveTestFacility wrairPlannedExpandedFacility1969
  expansionFacilityUnderConstructionReport koslovRand
  "Samuel Koslov 4 Nov 1969 described a new facility nearing completion with three extra exposure chambers and ancillary laboratories"
  "The 1969 state is contemporaneous description, not a completion record or evidence of post-1970 work; 1977 DARPA professed no knowledge of later rebuilding"

pandoraRetrospectiveAccountTension : BoundedLineageEdge
pandoraRetrospectiveAccountTension = boundedLineageEdge
  arpaPandora darpa1977DisavowalStatement disputedRetrospectiveCharacterisation heilmeier1977
  "DARPA director in 1977 denied awareness of DoD work probing microwave mind-control possibilities; Cesaro 1967 recorded recommendation to study possible weapon applications to behavioural effects"
  "The difference between a 1967 recommendation and a 1977 claim about actual sponsored projects prevents inferring a strict factual contradiction, deliberate deception, or operational capability"

-- 27 distinct dated publication/source objects in this consumer's current
-- source atlas. Count is documentary, not independent scientific studies.
sourceCarrierCountIsTwentySeven :
  Source.sourceCount (Source.sources sourceAtlas) ≡ 27
sourceCarrierCountIsTwentySeven = refl

-- Documentary possession, programme hardware, and experiment performance are
-- different kinds of object. Asset transfer does not prove transfer of data.
data RecordOrEquipmentKind : Set where
  rawExperimentalObservations : RecordOrEquipmentKind
  equipmentAssetForDisposition : RecordOrEquipmentKind
  agencyTechnicalReport : RecordOrEquipmentKind

assetTransferIsNotRawDataTransfer :
  equipmentAssetForDisposition ≡ rawExperimentalObservations → ⊥
assetTransferIsNotRawDataTransfer ()

agencyReportDoesNotResolveRawExperiment :
  agencyTechnicalReport ≡ rawExperimentalObservations → ⊥
agencyReportDoesNotResolveRawExperiment ()

pandoraApparatusActuallyConstructed : BoundedLineageEdge
pandoraApparatusActuallyConstructed = boundedLineageEdge
  arpaPandora walterReedMicrowaveTestFacility originalApparatusEngineeringReport byronFinal1966
  "JHU APL authored a genuine report on constructed 1966 Walter Reed laboratory electromagnetic exposure equipment and chamber test results"
  "Full archive bundle retrieval still pending; no novel clinical efficacy or transfer to present-day commercial RF infrastructure"

pandoraInitialAnimalReport : BoundedLineageEdge
pandoraInitialAnimalReport = boundedLineageEdge
  walterReedMicrowaveTestFacility originalPrimateHighDoseExperiment sourceReportedPreliminaryOutcome arpaInitial1966
  "ARPA memorandum reports a single initial primate under higher-intensity modulated RF and observed task slowdown"
  "No verified independent animal-level replication, direct neural endpoint, or effect at embassy dose"

pandoraCorrectedLevelNull : BoundedLineageEdge
pandoraCorrectedLevelNull = boundedLineageEdge
  originalPrimateHighDoseExperiment correctedLowDoseReplication subsequentDoseReassessment cesaroSeptember1967
  "ARPA reports normal comparable unmodulated performance and no overt degradation at tested weaker modulated levels; Moscow field reassessed <=0.05 mW/cm2"
  "The summary only captures task performance; source attribution does not prove zero biological effect in every tissue/dose or intention of any Soviet transmitter"

data ExperimentalOutcomeClaim : Set where
  overtTaskPerformance : ExperimentalOutcomeClaim
  directlyMeasuredNeuralResponse : ExperimentalOutcomeClaim
  humanControlledBehavior : ExperimentalOutcomeClaim

taskChangeIsNotDirectBrainMeasurement :
  overtTaskPerformance ≡ directlyMeasuredNeuralResponse → ⊥
taskChangeIsNotDirectBrainMeasurement ()

taskChangeIsNotHumanControl :
  overtTaskPerformance ≡ humanControlledBehavior → ⊥
taskChangeIsNotHumanControl ()

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


-- 2026-10-26 source-root cut: visually inspected US Senate 1979 committee
-- print pp. 10-11 (PDF pp. 16-17), which summarizes Kubis's 4 Dec 1969
-- review and the Jan 1970 SAC. This is a secondary *historical report*
-- of the same WRAIR primate research, not a fresh blinded replication:
-- https://nsarchive.gwu.edu/sites/default/files/documents/rhwvuj-tzy4b/15.pdf
-- The Senate's stated conclusion is that the original primate study did NOT
-- supply an acceptable answer to its causal question, due to contaminated
-- controls, malfunctioning apparatus and variable procedure. This is NOT
-- proof of a nonzero effect, a well-powered zero effect, or a modern device.
-- It coexists with recorded later trials failing to confirm an early report.

data PrimateInferenceStanding : Set where
  earlyPerformanceChangeReported : PrimateInferenceStanding
  laterTrialsDidNotConfirmEarlyChange : PrimateInferenceStanding
  originalDesignCannotIdentifyCausalEffect : PrimateInferenceStanding
  causalEffectIndependentlyEstablished : PrimateInferenceStanding
  trueZeroEffectIndependentlyEstablished : PrimateInferenceStanding

unidentifiedIsNotDemonstratedNull :
  originalDesignCannotIdentifyCausalEffect ≡
    trueZeroEffectIndependentlyEstablished → ⊥
unidentifiedIsNotDemonstratedNull ()

unidentifiedIsNotDemonstratedPositive :
  originalDesignCannotIdentifyCausalEffect ≡
    causalEffectIndependentlyEstablished → ⊥
unidentifiedIsNotDemonstratedPositive ()

failedConfirmationIsNotUniversalNull :
  laterTrialsDidNotConfirmEarlyChange ≡
    trueZeroEffectIndependentlyEstablished → ⊥
failedConfirmationIsNotUniversalNull ()

-- The *PANDORA primate review* section of the Senate committee report
-- is a later publication carrier of the earlier SAC/Kubis review. This
-- quotient is intentionally restricted to this review's original animal
-- evidence; other independent studies compiled in the 1979 Senate volume
-- retain their own provenance (Big Boy, GWU, Lilienfeld, lymphocytes).
data WrairReviewCarrier : Set where
  pandoraSACOriginal1970 : WrairReviewCarrier
  senateCompilation1979PrimateSection : WrairReviewCarrier

data WrairOriginalPrimateEvidenceRoot : Set where
  wrair1960sExperimentalRecord : WrairOriginalPrimateEvidenceRoot

wrairOriginalEvidence : WrairReviewCarrier → WrairOriginalPrimateEvidenceRoot
wrairOriginalEvidence _ = wrair1960sExperimentalRecord

senateDoesNotReplicateWrairPrimates :
  wrairOriginalEvidence pandoraSACOriginal1970 ≡
  wrairOriginalEvidence senateCompilation1979PrimateSection
senateDoesNotReplicateWrairPrimates = refl

senate1979PrimateStudyInconclusive : BoundedLineageEdge
senate1979PrimateStudyInconclusive = boundedLineageEdge
  originalPrimateHighDoseExperiment pandora1970CommitteeFinalReassessment
  committeeOriginalStudyReassessment senateMoscow1979
  "US Senate 1979 original committee print pp. 10-11, after recounting McIlwain's failed-to-confirm trials at 4.6 and 20 mW/cm2, summarizes Kubis and SAC: the earlier primate design did not give an acceptable answer because baseline controls and experimental conditions were contaminated"
  "The Senate compilation is NOT another primate trial; failure of causal identification cannot be treated as a reliable positive effect or as a demonstrated universal negative. Prospective deliberate human irradiation was not carried out according to the same report"
