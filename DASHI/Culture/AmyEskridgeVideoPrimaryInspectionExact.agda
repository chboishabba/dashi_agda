module DASHI.Culture.AmyEskridgeVideoPrimaryInspectionExact where

-- DASHI-native reinspection of source evidence for the 2026-05-12 Be Inspired
-- upload https://www.youtube.com/watch?v=acw16d6CCnY (32:47).
-- Source identification from channel indices; user transcript through 32:44.
-- Original documents: NASA NTRS 20000038203, 19990039542, 19990019627;
-- Physica C 203(1992) DOI 10.1016/0921-4534(92)90055-H;
-- DIA FOIA-00159-2018 letter 2022-03-25, DIRD 13/15/18/19;
-- Bem JPSP 100(3) 2011 DOI 10.1037/a0021524.
-- Each record states the exact inspection scope and which proposition is paid.
-- 'Inspected' is a *source reading*, not Agda verification or proof that
-- experimental results are reproducible. Follow Docs/SourceAttributionPolicy.
-- External source assertions are NEVER attributed to DASHI as discoveries.
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)
import DASHI.Culture.AmyEskridgeVideoClaimAttributionLedgerExact as Video
import DASHI.Culture.AmyEskridgeVideoClaimProducerWeldExact as Existing

data InspectionExtent : Set where
  inspectedDocument : InspectionExtent
  abstractInspected : InspectionExtent
  clipIdentified : InspectionExtent
  unresolved : InspectionExtent

record PrimaryDocumentReading : Set where
  constructor primary-document-reading
  field
    videoTime : String
    sourceCreators : String
    originalTitle : String
    exactReference : String
    sourceURL : String
    inspectionExtent : InspectionExtent
    strictlyPaidProposition : String
    expresslyUnpaidPromotion : String
    nextPrimaryReceipt : String
open PrimaryDocumentReading public

ningNASAagreement : PrimaryDocumentReading
ningNASAagreement = primary-document-reading
  "09:55-10:16"
  "Ning Li"
  "Cooperative Agreement NCC8-124 NASA/MSFC and UAH Final Report"
  "NASA NTRS 20000038203, pp. 1-3, dated 1996-12-04 through 2000-12-03"
  "https://ntrs.nasa.gov/api/citations/20000038203/downloads/20000038203.pdf"
  inspectedDocument
  "Two usable 12-inch YBCO 1-2-3 disks fabricated; NASA-UAH final all-up gravity measurements not completed in agreement term"
  "successful antigravity, transfer to later Army programme, cause of Ning Li death"
  "NASA-MSFC/UAH instrumentation follow-up, later Army SOW and reports"

ning1997static : PrimaryDocumentReading
ning1997static = primary-document-reading
  "09:30-10:02"
  "Ning Li; David Noever; Tony Robertson; Ron Koczor; Whitt Brantley"
  "Static test for a gravitational force coupled to type II YBCO superconductors"
  "Physica C 281 (1997) 260-267 DOI 10.1016/S0921-4534(97)01462-7; NASA NTRS 19990039542"
  "https://ntrs.nasa.gov/citations/19990039542"
  abstractInspected
  "Static superconductor gravimeter change less than 2 parts in 10^8 of normal acceleration; a bounded negative constraint"
  "all rotating rigs; all possible superconductor-gravity couplings; propulsion"
  "Detailed experimental conditions and independent replication"

nasaRotating1998 : PrimaryDocumentReading
nasaRotating1998 = primary-document-reading
  "10:43-11:17"
  "David A. Noever; Ronald J. Koczor; Rick Roberson"
  "Superconductor-Mediated Modification of Gravity? AC Motor Experiments with Bulk YBCO Disks in Rotating Magnetic Fields"
  "NASA NTRS 19990019627, publication 1998"
  "https://ntrs.nasa.gov/citations/19990019627"
  abstractInspected
  "15 cm YBCO disk in three-phase AC motor stator; up to 12,000 rpm rotating field; no gravimeter effect detected within tested precision"
  "universal negative proof of effect in all apparatus and regimes; independent replicated 2 percent"
  "Full paper and exact uncertainty/control model"

podkletnov1992 : PrimaryDocumentReading
podkletnov1992 = primary-document-reading
  "10:43-11:17"
  "E. Podkletnov; R. Nieminen"
  "A possibility of gravitational force shielding by bulk YBa2Cu3O7-x superconductor"
  "Physica C 203 (1992) 441-444 DOI 10.1016/0921-4534(92)90055-H"
  "https://doi.org/10.1016/0921-4534(92)90055-H"
  abstractInspected
  "Authors report 0.05-0.3 percent apparent weight decrease of 5.48 g sample above superconducting disk"
  "later reports up to 2.1 percent; physical replication, government suppression"
  "Locate later Podkletnov experiment and physical controls, independent replication"

diaFOIA2022 : PrimaryDocumentReading
diaFOIA2022 = primary-document-reading
  "13:42-15:28"
  "U.S. Defense Intelligence Agency; John Greenewald FOIA requester"
  "FOIA-00159-2018 release and 37-document inventory"
  "DIA U-22-7061/IMO-2 March 25 2022, page 1 and attachment"
  "https://documents2.theblackvault.com/documents/dia/AAWSAP-DIRDs/FOIA%2000159-2018.pdf"
  inspectedDocument
  "DIA identified 37 responsive Defense Intelligence Reference Documents (1,473 pages) for March 2022 release; inventory identifies four named studies as 13, 15, 18, 19"
  "claim that 38 full reports were released in that same FOIA response; technology built or tested"
  "Reconcile earlier 38-title listing with this 37-document release, find 38th status"

diaWarp : PrimaryDocumentReading
diaWarp = primary-document-reading
  "14:40-15:01"
  "U.S. Defense Intelligence Agency; author not inferred from redacted cover"
  "Warp Drive, Dark Energy, and the Manipulation of Extra Dimensions"
  "DIA-08-1004-001, 2 April 2010, Section 8 p.24"
  "https://documents2.theblackvault.com/documents/dia/AAWSAP-DIRDs/DIRD_13-DIRD_Warp_Drive_Dark_energy_and_the_Manipulation_of_Extra_Dimensions.pdf"
  inspectedDocument
  "Theoretical model of extra-dimension/dark-energy control and possible warp propulsion; summary says not actualized and prospective"
  "actual warp bubble creation, spacetime manipulation or operational vehicle"
  "Source-to-dynamics producer, measurements of actual metric engineering"

diaVacuum : PrimaryDocumentReading
diaVacuum = primary-document-reading
  "15:10-15:23"
  "U.S. Defense Intelligence Agency; author not inferred from redacted cover"
  "Advanced Space Propulsion Based on Vacuum (Spacetime Metric) Engineering"
  "DIA-08-1003-015, 29 March 2010, preface and section IV pp. iii, 11"
  "https://documents2.theblackvault.com/documents/dia/AAWSAP-DIRDs/DIRD_15-DIRD_Advanced_Space_Propulsion_Based_on_Vacuum_Spacetime_Metric_Engineer.pdf"
  inspectedDocument
  "Model-independent metric tensor parameterization assuming technology that can engineer spacetime; notes present required energy densities many orders beyond available engineering"
  "working vacuum thruster, extraction of net free energy, practical spacecraft"
  "Identify actual stress-energy sources and observed metric/energy balance"

diaWormholes : PrimaryDocumentReading
diaWormholes = primary-document-reading
  "14:14-14:40"
  "U.S. Defense Intelligence Agency; author not inferred from redacted cover"
  "Traversable Wormholes, Stargates, and Negative Energy"
  "DIA-08-1004-004, 6 April 2010, Section V p.26"
  "https://documents2.theblackvault.com/documents/dia/AAWSAP-DIRDs/DIRD_18-DIRD_Traversible_Wormholes_Stargates_and_Negative_Energy.pdf"
  inspectedDocument
  "Theoretical discussion of wormhole spacetime and energy requirements; closing section calls for future laboratory demonstrations"
  "actual Stargate device, P45/P52 testimony or existing wormhole travel"
  "Physical construction, negative-energy quantity, independent lab detection"

diaAntigravity : PrimaryDocumentReading
diaAntigravity = primary-document-reading
  "15:01-15:10"
  "U.S. Defense Intelligence Agency; author not inferred from redacted cover"
  "Antigravity for Aerospace Applications"
  "DIA-08-1003-018, 30 March 2010, Section V pp.24-25"
  "https://documents2.theblackvault.com/documents/dia/AAWSAP-DIRDs/DIRD_19-DIRD_Antigravity_for_Aerospace_Applications.pdf"
  inspectedDocument
  "Review evaluates speculative gravitation and vacuum-force approaches; conclusion says daunting technical challenges, technology for useful densities/velocities absent"
  "achieved antigravity aerospace generator, classified operational technology"
  "Same-object apparatus, measured force controls, reproducibility"

bem2011 : PrimaryDocumentReading
bem2011 = primary-document-reading
  "18:35-19:10"
  "Daryl J. Bem"
  "Feeling the Future: Experimental Evidence for Anomalous Retroactive Influences on Cognition and Affect"
  "JPSP 100(3) (2011) 407-425 DOI 10.1037/a0021524; PMID 21280961"
  "https://pubmed.ncbi.nlm.nih.gov/21280961/"
  abstractInspected
  "Nine psychology tasks reported retroactive effects; NOT exactly the anticipatory physiology protocol quoted by the video narrator"
  "independent reproducibility, physiological pre-stimulus clip provenance, machine future viewing"
  "Precise clip recording and distinct presentiment experimental DOI/protocol/replications"

originalDocumentsInspected : List PrimaryDocumentReading
originalDocumentsInspected =
  ningNASAagreement ∷
  ning1997static ∷
  nasaRotating1998 ∷
  podkletnov1992 ∷
  diaFOIA2022 ∷
  diaWarp ∷
  diaVacuum ∷
  diaWormholes ∷
  diaAntigravity ∷
  bem2011 ∷ []

-- This ledger is a refinement of the existing all-86 source join, not a
-- substitute or alternate source of individual claims.
existingVideoClaimUniverse : List Video.RawAttributedClaim
existingVideoClaimUniverse = Video.transcriptClaims

all86SourceAssociationRetained :
  Existing.forgetProducer Existing.allVideoClaimJoins ≡ existingVideoClaimUniverse
all86SourceAssociationRetained = Existing.all86RowsAccountedFor

-- No conversion from inspected bibliography, report or patent to scientific
-- mechanism proof, same-person identity or unverified forensic causality.
data InspectionCreatesExperimentalReplication : Set where
data ReportReleaseProvesSecretMachinery : Set where
data AttributionToVideoProvesHarm : Set where

noReplicateByBibliography : InspectionCreatesExperimentalReplication → ⊥
noReplicateByBibliography ()

noSecretTechnologyFromFOIA : ReportReleaseProvesSecretMachinery → ⊥
noSecretTechnologyFromFOIA ()

noResearchToDeathPromotion : AttributionToVideoProvesHarm → ⊥
noResearchToDeathPromotion ()
