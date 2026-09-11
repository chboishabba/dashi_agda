module DASHI.Culture.MissingDeceasedIbrahimInvestigativeParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- IBRAHIM-GUIDED INVESTIGATIVE PARETO ROUTING
--
-- Thin ranking surface only.  It does not replace person-specific acquisition
-- owners or create a generic planner.  Ibrahim-style graph traversal ranks the
-- smallest set of primary-object searches expected to collapse the largest
-- number of already-typed unpaid leaves.  Evidence authority remains with the
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
  "Highest fan-out because one jurisdictional entity-history record can distinguish same-name firms and settle whether the Tegnelia/McCasland manifestations concern one legal entity before any client or programme inference."

amyReleaseMetadataPareto : InvestigativeParetoTarget
amyReleaseMetadataPareto = investigative-pareto-target
  firstFront
  "Amy Eskridge / POAMS"
  "technical report Q3099732 -> research/report administration -> STI/release metadata"
  "MSFC STI release-authorisation object: exact POAMS EDAA/NF-1676B plus attached reviewed manuscript/version"
  "NTRS 20205010911; NASA/TM-20205010911; M-1531; SAA8-1519855; funding MSFC-RMB-QUANTUM-SAA8-1519855-1; Propulsion Systems Department / Engineering Directorate"
  "review-object identity; release-history identity; attachment/version identity; Amy O2<->public-TM same-object test; route toward Institute derivative identity"
  "NTRS 20205010911; NASA/TM-20205010911; M-1531; exact EDAA unresolved"
  "NASA Q23548; MSFC Q618696; report-domain QID only as traversal"
  "NASA Subject Category 70 / 530 Physics; metadata traversal 025.3 / 005.7 only"
  "primary NASA/MSFC STI compliance or release-authorisation record"
  true true false
  "Public NTRS metadata is exhausted without the EDAA. One exact release object could join the administrative release chain, reviewed manuscript/version and the Amy same-object comparison without inventing a hidden-record conclusion from public-search failure."

rezaIdentityAndRolePareto : InvestigativeParetoTarget
rezaIdentityAndRolePareto = investigative-pareto-target
  secondFront
  "Monica Jacinto Reza / materials processing"
  "patent Q253623 -> intellectual property Q131257 -> assignment/inventor identity; separate JPL personnel branch"
  "primary carrier explicitly tying patent inventor Monica A. Jacinto to Monica Andrea Jacinto/Reza; independently, JPL/Caltech personnel/directory/org-chart record for Materials Processing role"
  "US20030053926A1 facsimile = Monica A. Jacinto; US20040208777A1 2004 Boeing assignment by Monica A. Jacinto; Boeing 2004 and Cal State 2021 Monica Jacinto professional lineage; California DOJ Monica Jacinto Reza AKA Monica Andrea Jacinto"
  "patent-person identity weld; employer lineage; event-time JPL role; eligibility for process-window/custody/succession promotion"
  "US20030053926A1; US20040208777A1; LASD 025-00905-1257-400; Q139385030 traversal only"
  "Monica Jacinto Q139385030; patent Q253623; intellectual property Q131257"
  "346.048 Intellectual property / 620 Engineering traversal only"
  "primary patent/person identity record plus primary JPL/Caltech institutional personnel record"
  true true false
  "The patent/IP route has already replaced rendered-name inference with source-text and assignment carriers. The remaining high-value join is explicit A.-to-Andrea identity, while the JPL role must remain independently institution-paid."

maiwaldDataPareto : InvestigativeParetoTarget
maiwaldDataPareto = investigative-pareto-target
  secondFront
  "Frank W. Maiwald / action spectroscopy"
  "research data Q15809982 -> data Q42848; metadata Q180160 -> repository/deposit manifestation"
  "raw/reduced ion-action spectroscopy dataset or repository/deposit object with version/figure crosswalk to FY23 poster, ChemRxiv, ACS SI and 2025 publication"
  "JPL FY23/FY24 project carriers; DOI 10.1021/acs.jpca.4c03552; ChemRxiv 10.26434/chemrxiv-2024-2tvc6; NTRS 13797709699197 CHORUS harvest; DOI 10.1021/acs.jpca.5c03141"
  "raw-data identity; reduction lineage; figure provenance; data custody; manifestation-affiliation production history"
  "ACS/ChemRxiv DOIs above; NTRS 13797709699197; person QID unresolved; JPL Q189325 institution only"
  "research data Q15809982; data Q42848; metadata Q180160; JPL Q189325 institution only"
  "543.5 Spectroscopy / 540 Chemistry; metadata traversal only"
  "primary repository/deposit or instrument/data-management record"
  false true false
  "Publication and harvest manifestations are now well mapped, so another article has low marginal value. A deposit or instrument-level dataset identity would collapse the largest remaining scientific-custody subtree."

leblancFreezePareto : InvestigativeParetoTarget
leblancFreezePareto = investigative-pareto-target
  thirdFront
  "Joshua LeBlanc / SNP I&C TechMat"
  "metadata Q180160 -> version/freeze/governance manifestation"
  "recognition-slide internal freeze/authorship date or first exact post-loss TechMat roster/governance artifact"
  "NTRS 20250008475; acquired 2025-08-16; webinar 2025-08-26; WBS 658133.04.01.22.01.06; DOI 10.13182/NPICHMIT25-46370 is a distinct pre-loss publication"
  "role-state chronology; whether stale slide label predates loss; exact successor/handover search routing"
  "NTRS 20250008475; WBS 658133.04.01.22.01.06; DOI 10.13182/NPICHMIT25-46370"
  "person QID unresolved; metadata Q180160 traversal only"
  "621 Applied physics / 629 Engineering; metadata traversal only"
  "primary NASA version/freeze metadata or dated programme roster"
  false true false
  "The public object is already a post-loss manifestation that still names LeBlanc. Freeze/authorship metadata is narrower than the first-front targets but can decisively separate manifestation date from role-state date."

loureiroFormalSuccessionPareto : InvestigativeParetoTarget
loureiroFormalSuccessionPareto = investigative-pareto-target
  retainedParallel
  "Nuno F. Loureiro / student and resource succession"
  "metadata/administrative record -> advisor, repository and allocation governance"
  "formal MIT advisor-of-record/thesis-committee reassignment and exact repository/dataset object; resource-allocation administration only where person-specific"
  "DOI 10.1017/S002237782510113X; arXiv 2505.08983; Dion Li post-loss DOI 10.1103/j5p4-jj3d; institutional resource reuse DE-FG02-91ER54109 and NERSC FES-ERCAP0026577 already separated from PI transfer"
  "formal advisor succession; repository custody; same-simulation-state question; person-specific versus institutional resource continuity"
  "Q51287446; DOI/arXiv identifiers above; DOE/NERSC identifiers are resource coordinates, not transfer receipts"
  "Loureiro Q51287446"
  "530 Physics"
  "primary MIT graduate-programme/advisor record and primary repository/dataset record"
  false true false
  "Scientific continuation and institutional resource continuity are already paid. The remaining high-alpha work is administrative succession, so broad publication snowballing has low marginal value."

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
