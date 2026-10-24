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
import DASHI.Governance.InstitutionalAnomalousAlteredStateProgramAtlasExact as History

mkUltraOwner : History.ProgrammeFamily
mkUltraOwner = History.mkultraMksearchFamily

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
  (mk119Memo ∷ cesaroPandora ∷ johnstonBizarre ∷ pandoraHumanMinutes ∷
   koslovRand ∷ odniExperts ∷ odni2025 ∷ recall2026 ∷ [])
  "Bounded original-document roots, no fabricated modern source-to-device bridge"

sourceAtlasNeverPromotes :
  Source.attributedSourceAtlasReceiptNonPromoting sourceAtlas
    "No current same-actor apparatus or clinical exposure link is recovered" ≡ refl
sourceAtlasNeverPromotes = refl

-- Named research objects. Topic similarity cannot be promoted to same project.
data ProgrammeObject : Set where
  mkUltraSubproject119 : ProgrammeObject
  arpaPandora : ProgrammeObject
  arpaBizarre : ProgrammeObject
  modernAnomalousHealthInquiry : ProgrammeObject

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
