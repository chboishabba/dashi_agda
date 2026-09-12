module DASHI.Culture.MissingDeceasedIbrahimInvestigativeParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- IBRAHIM-GUIDED INVESTIGATIVE PARETO ROUTING
--
-- Thin ranking surface only. It does not replace person-specific acquisition
-- owners or create a generic planner. Ibrahim-style graph traversal ranks the
-- smallest set of primary-object searches expected to collapse the largest
-- number of already-typed unpaid leaves. Evidence authority remains with the
-- source-specific owners.
--
-- Ibrahim attribution:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI 10.1016/j.jocs.2016.12.001; arXiv:1605.00309.
------------------------------------------------------------------------

data ParetoPriority : Set where
  firstFront secondFront thirdFront retainedParallel : ParetoPriority

record InvestigativeParetoTarget : Set where
  constructor investigative-pareto-target
  field
    priority : ParetoPriority
    lane : String
    graphRoute : String
    exactPrimaryTarget : String
    currentlyPaidCoordinates : String
    uncertaintyFanOut : String
    stableIdentifiersOrRegistryKeys : String
    qidCoordinates : String
    deweyTraversal : String
    primarySourceClassRequired : String
    currentPublicSearchWall : Bool
    oneObjectMayCloseMultipleLeaves : Bool
    graphRouteCreatesEvidenceAuthority : Bool
    acquisitionReading : String

open InvestigativeParetoTarget public

mccaslandEntityHistoryPareto : InvestigativeParetoTarget
mccaslandEntityHistoryPareto = investigative-pareto-target
  firstFront
  "William Neil McCasland / DBE Consulting"
  "company register Q134611895; broader trade-register coordinate Q1394657 -> company/legal entity"
  "New Mexico jurisdictional company/entity-history object identifying exact DBE Consulting LLC entity ID, formation, members/managers and dated ownership/role changes"
  "2011 U.S. State Department: James A. Tegnelia = President and Owner; 2017 DBE Albuquerque letterhead; current Kirtland duplicate Founder/Owner/President headings; unrelated Atlanta same-label company retained as collision control"
  "entity identity; same-company weld across manifestations; founder attribution; ownership chronology; McCasland event-time corporate role; admissibility of later client/contract search"
  "jurisdictional legal-entity identifier unresolved; Albuquerque address 11039 Bridgepointe NE retained as query coordinate"
  "company register Q134611895; trade register Q1394657; person QIDs unresolved"
  "338.7 Enterprises / 650 Management traversal only"
  "primary government company-register/entity-history record"
  true true false
  "Highest fan-out, but the indexed public web has reached a source-class wall: one official New Mexico entity-history record could distinguish same-name firms and settle whether the Tegnelia/McCasland manifestations concern one legal entity before any client or programme inference."

amyReleaseMetadataPareto : InvestigativeParetoTarget
amyReleaseMetadataPareto = investigative-pareto-target
  firstFront
  "Amy Eskridge / POAMS"
  "technical report Q3099732 -> research/report administration -> STI/release metadata"
  "MSFC STI release-authorisation object: POAMS NF-1676/STRIVES approval identity, attached reviewed manuscript/version, review-history metadata, and any migrated legacy EDAA/NF-1676B lineage"
  "NTRS 20205010911; NASA/TM-20205010911; M-1531; SAA8-1519855; funding MSFC-RMB-QUANTUM-SAA8-1519855-1; Propulsion Systems Department / Engineering Directorate; STRIVES fully adopted agency-wide by 2020-05, NTRS transitioned by 2020-07, legacy STI applications retired by 2020-08; POAMS acquired 2020-12-01"
  "review-object identity; release-history identity; attachment/version identity; legacy-to-current release-record crosswalk; Amy O2<->public-TM same-object test; route toward Institute derivative identity"
  "NTRS 20205010911; NASA/TM-20205010911; M-1531; exact NF-1676/STRIVES approval identity unresolved; legacy EDAA retained as predecessor lineage only unless a primary record proves otherwise"
  "NASA Q23548; MSFC Q618696; report-domain QID only as traversal"
  "NASA Subject Category 70 / 530 Physics; metadata traversal 025.3 / 005.7 only"
  "primary NASA/MSFC STI compliance or release-authorisation record"
  true true false
  "Public NTRS/title/report/funding/author searches are exhausted without the approval record. Because POAMS falls after NASA's 2020 STRIVES migration, the preferred primary target is the NF-1676/STRIVES-era approval identity and attached STI/version; a legacy EDAA is sought only as migration/predecessor archaeology, not assumed as the active late-2020 namespace."

rezaIdentityAndRolePareto : InvestigativeParetoTarget
rezaIdentityAndRolePareto = investigative-pareto-target
  secondFront
  "Monica Jacinto Reza / materials processing"
  "patent Q253623 -> intellectual property Q131257 -> assignment/inventor identity; separate JPL personnel branch"
  "primary carrier explicitly tying patent inventor Monica A. Jacinto to Monica Andrea Jacinto/Reza; independently, archived 2024-2025 Cal State LA board manifestation or JPL/Caltech personnel/directory/org-chart record for Materials Processing role"
  "US20030053926A1 facsimile = Monica A. Jacinto; US20040208777A1 2004 Boeing assignment by Monica A. Jacinto; Boeing 2004, Cal State 2021 and AIAA SciTech 2023 Monica Jacinto/Aerojet lineage; California DOJ Monica Jacinto Reza AKA Monica Andrea Jacinto; current 2025-2026 Cal State board does not expose the reported 2024-2025 row"
  "patent-person identity weld; employer-transition interval; event-time JPL role; eligibility for process-window/custody/succession promotion"
  "US20030053926A1; US20040208777A1; AIAA 99-2754; AIAA SciTech 2023 primary Aerojet carrier; LASD 025-00905-1257-400; Q139385030 traversal only"
  "Monica Jacinto Q139385030; patent Q253623; intellectual property Q131257"
  "346.048 Intellectual property / 620 Engineering traversal only"
  "primary patent/person identity record plus primary archived Cal State or JPL/Caltech institutional personnel record"
  true true false
  "The public indexed surface is exhausted at the institutional transition. Primary records place Monica Jacinto at Aerojet through the 2023 conference cycle; secondary sources repeat a 2024-2025 Cal State row saying Monica Reza / JPL NASA, but that archived primary manifestation and a JPL personnel object remain unrecovered. Repetition cannot pay the transition."

maiwaldDataPareto : InvestigativeParetoTarget
maiwaldDataPareto = investigative-pareto-target
  secondFront
  "Frank W. Maiwald / action spectroscopy"
  "spectroscopy Q483666 -> research data Q15809982 -> data Q42848; metadata Q180160 -> scan/deposit/instrument manifest"
  "scan-level wavelength/intensity assets, reduced-spectrum tables or instrument/data-management manifest crosswalking the multi-day ValH+·N2 / ValH+·CH4 acquisition to Figure 3, the FY23 JPL poster and later publication manifestations"
  "JPL FY23/FY24 project carriers; DOI 10.1021/acs.jpca.4c03552; ChemRxiv 10.26434/chemrxiv-2024-2tvc6; NSF PAR purl 10612041 full manuscript; NTRS 13797709699197 CHORUS harvest; DOI 10.1021/acs.jpca.5c03141; ACS supporting-information assets are exposed through Figshare-backed presentation but contain calculated/derived material rather than an identified raw instrument dataset"
  "exact raw-scan identity; reduction lineage; Figure-3 provenance; raw/reduced data custody; poster-to-publication same-data crosswalk; manifestation-affiliation production history"
  "NSF PAR 10612041; 10.1021/acs.jpca.4c03552; 10.26434/chemrxiv-2024-2tvc6; NTRS 13797709699197; 10.1021/acs.jpca.5c03141; JPL/NASA prime contract 80NM0018D0004; NSF CHE-2154271; CU ACI-1532235 / ACI-1532236; person QID unresolved"
  "research data Q15809982; data Q42848; metadata Q180160; spectroscopy Q483666; JPL Q189325 institution only"
  "543.5 Spectroscopy / 540 Chemistry; metadata traversal only"
  "primary scan/data repository, reduced-table deposit, instrument log or data-management manifest"
  true true false
  "The indexed public repository/publication surface is exhausted: article, ChemRxiv, ACS SI/Figshare presentation, NASA/CHORUS and NSF-PAR manuscript manifestations are mapped, but no title-matched raw/reduced spectra deposit or instrument manifest surfaced. Another manuscript copy has negligible value; the next source class is a repository/instrument log or author/lab data-management carrier."

leblancFreezePareto : InvestigativeParetoTarget
leblancFreezePareto = investigative-pareto-target
  thirdFront
  "Joshua LeBlanc / SNP I&C TechMat"
  "metadata Q180160 -> version/freeze/governance manifestation"
  "recognition-slide internal freeze/authorship date or first exact post-loss TechMat roster/governance artifact"
  "NTRS 20250008475; acquired 2025-08-16; webinar 2025-08-26; NASA Peer Committee review; WBS 658133.04.01.22.01.06; DOI 10.13182/NPICHMIT25-46370 distinct pre-loss publication; later NTRS 20240010391 uses the same WBS for a 2026-05-27 Glenn sensor meeting"
  "role-state chronology; same-WBS programme continuity versus person-role continuity; exact successor/handover search routing"
  "NTRS 20250008475; WBS 658133.04.01.22.01.06; DOI 10.13182/NPICHMIT25-46370; NTRS 20240010391"
  "person QID unresolved; metadata Q180160 traversal only"
  "621 Applied physics / 629 Engineering; metadata traversal only"
  "primary NASA version/freeze metadata or dated programme roster"
  true true false
  "Exact current searches collapse back to the same post-loss NTRS deck. The public repository pays acquisition/review chronology and continued same-WBS programme activity but exposes no slide-authorship/freeze date and no exact post-loss TechMat roster. The next source class is internal NASA version/governance metadata, not more topical I&C publications."

loureiroFormalSuccessionPareto : InvestigativeParetoTarget
loureiroFormalSuccessionPareto = investigative-pareto-target
  retainedParallel
  "Nuno F. Loureiro / student and resource succession"
  "metadata/administrative record -> advisor, repository and allocation governance"
  "formal MIT advisor-of-record/thesis-committee reassignment and exact repository/dataset object; resource-allocation administration only where person-specific"
  "DOI 10.1017/S002237782510113X; arXiv 2505.08983; Dion Li post-loss DOI 10.1103/j5p4-jj3d; MIT identifies Dion Li as Loureiro PhD student; PSFC report page says associated Dataverse datasets exist if applicable; Cambridge directs supporting-data requests to Dion Li; Simran Chowdhry remains a current MIT graduate student and Oxford 2026 says she works on her PhD there for a term with Dmitri Uzdensky; institutional resource reuse DE-FG02-91ER54109 and NERSC FES-ERCAP0026577 already separated from PI transfer"
  "formal advisor succession; repository custody; same-simulation-state question; person-specific versus institutional resource continuity"
  "Q51287446; DOI/arXiv identifiers above; DOE/NERSC identifiers are resource coordinates, not transfer receipts"
  "Loureiro Q51287446"
  "530 Physics"
  "primary MIT graduate-programme/advisor record and primary repository/dataset record"
  true true false
  "Scientific continuation, corresponding-author data access, external research supervision and institutional resource continuity are already paid. Exact searches still expose no MIT advisor-of-record/thesis-committee reassignment and no title-matched Dataverse dataset object. The remaining route has therefore crossed into MIT graduate-administration and repository-record acquisition rather than public publication discovery."

------------------------------------------------------------------------
-- Pareto boundary: ranking is operational, not probabilistic or evidentiary.
------------------------------------------------------------------------

record InvestigativeParetoBoundary : Set where
  constructor investigative-pareto-boundary
  field
    priorityMeansCausalProbability : Bool
    priorityMeansSubjectImportance : Bool
    fanOutEstimateCreatesEvidenceAuthority : Bool
    graphRouteCreatesEvidenceAuthority : Bool
    onePrimaryObjectMayCloseSeveralTypedLeaves : Bool
    laterEvidenceMayBeRetainedOutOfDependencyOrder : Bool
    paymentMaySkipIdentityOrSameObjectDependencies : Bool

open InvestigativeParetoBoundary public

canonicalInvestigativeParetoBoundary : InvestigativeParetoBoundary
canonicalInvestigativeParetoBoundary = investigative-pareto-boundary
  false false false false true true false
