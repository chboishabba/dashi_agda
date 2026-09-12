module DASHI.Culture.MissingDeceasedInvestigativeAttributedSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.AttributedSourceCore as A

------------------------------------------------------------------------
-- INVESTIGATIVE ATTRIBUTED SOURCE ATLAS
--
-- Every entry states exactly what relationship it may support.  The atlas is
-- deliberately non-promoting: a URL, citation, discovery lead, news report or
-- source repetition cannot become proof, causal authority, same-object identity
-- or forensic fact by being listed here.
------------------------------------------------------------------------

nasaNingNCC8124Source : A.AttributedSource
nasaNingNCC8124Source = A.mkNoDOISource
  "Ning Li"
  "Activities of UAH"
  "NASA Technical Reports Server, document 20000038203"
  "2000"
  "https://ntrs.nasa.gov/citations/20000038203"
  A.governmentSource
  "primary NASA/MSFC grantee-report manifestation for cooperative agreement NCC8-124; supports programme identity, funding/source metadata and the reported incomplete all-up experiment state; does not pay the later Army programme or a positive antigravity result"
  A.publicAttribution

ningYBCO1997Source : A.AttributedSource
ningYBCO1997Source = A.mkDOISource
  "Ning Li; G. A. Noever; T. Robertson; R. Koczor; W. Brantley"
  "Static test for a gravitational force coupled to type II YBCO superconductors"
  "Physica C: Superconductivity"
  "1997"
  "10.1016/S0921-4534(97)01462-7"
  "https://www.sciencedirect.com/science/article/pii/S0921453497014627"
  A.academicArticleSource
  "primary publication identity for the static YBCO gravimeter constraint; supports the tested-regime upper bound only and is not positive antigravity evidence"
  A.publicAttribution

rezaEarlyPatentSource : A.AttributedSource
rezaEarlyPatentSource = A.mkNoDOISource
  "Monica Jacinto; Dallis Hardwick"
  "Burn-resistant and high tensile strength metal alloys"
  "United States patent publication US20030053926A1"
  "2003"
  "https://patents.google.com/patent/US20030053926A1/en"
  A.governmentSource
  "primary patent manifestation for the early Jacinto/Hardwick composition box, element-role statements, VIM/VAR/mechanical-work process and tested oxygen/tensile examples; it does not establish a single-crystal article, metamaterial architecture, ITAR status, S4 provenance or a McCasland programme edge"
  A.publicAttribution

rezaPatentSource : A.AttributedSource
rezaPatentSource = A.mkNoDOISource
  "Monica A. Jacinto; Dallis E. Hardwick et al."
  "Burn-resistant and high tensile strength metal alloys"
  "United States patent publication US20100266442A1 and family"
  "2010"
  "https://patents.google.com/patent/US20100266442A1/en"
  A.governmentSource
  "primary later patent-family manifestation for composition/process/trade-off claims and inventor attribution; it does not by itself establish a single-crystal architecture, a metamaterial classification, ITAR status, S4 provenance or McCasland programme participation"
  A.publicAttribution

nasaFusionDrivenRocketSource : A.AttributedSource
nasaFusionDrivenRocketSource = A.mkNoDOISource
  "NASA TechPort"
  "The Fusion Driven Rocket"
  "NASA TechPort"
  "current public manifestation"
  "https://techport.nasa.gov/projects/11570"
  A.governmentSource
  "official programme source for fusion/magnetized-plasma propulsion domain topology; does not create named-person participation"
  A.publicAttribution

nasaDirectFusionDriveSource : A.AttributedSource
nasaDirectFusionDriveSource = A.mkNoDOISource
  "NASA TechPort"
  "Fusion-Enabled Pluto Orbiter and Lander / Direct Fusion Drive"
  "NASA TechPort"
  "current public manifestation"
  "https://techport.nasa.gov/projects/93869"
  A.governmentSource
  "official programme source for FRC fusion, spacecraft power/propulsion and magnetic-nozzle engineering; does not weld Loureiro, Reza, Amy or Ning Li to the programme"
  A.publicAttribution

nasaAneutronicFusionSource : A.AttributedSource
nasaAneutronicFusionSource = A.mkNoDOISource
  "NASA TechPort"
  "Aneutronic Fusion Spacecraft Architecture"
  "NASA TechPort"
  "current public manifestation"
  "https://techport.nasa.gov/projects/4373"
  A.governmentSource
  "official programme source for aneutronic fusion-spacecraft architecture; supports a technology-domain bridge only"
  A.publicAttribution

nasaQuantumVacuumMentionSource : A.AttributedSource
nasaQuantumVacuumMentionSource = A.mkNoDOISource
  "NASA TechPort"
  "Direct Energy Conversion for Nuclear Propulsion at Low Specific Mass"
  "NASA TechPort project 12110"
  "historical/current public manifestation"
  "https://techport.nasa.gov/projects/12110"
  A.governmentSource
  "official historical programme wording that mentions a Quantum Vacuum thruster among possible propulsion partners; not a demonstration, validation or zero-point-energy extraction receipt"
  A.publicAttribution

houseOversightSource : A.AttributedSource
houseOversightSource = A.mkNoDOISource
  "U.S. House Committee on Oversight and Government Reform"
  "Comer & Burlison Seek Information on Missing Nuclear and Rocket Scientists"
  "House Oversight press release"
  "2026"
  "https://oversight.house.gov/release/comer-burlison-seek-information-on-missing-nuclear-and-rocket-scientists/"
  A.governmentSource
  "primary inquiry-scope manifestation; pays the existence and wording of the congressional inquiry but not a common cause, culprit, espionage theory or UAP theory"
  A.publicAttribution

nmDPSAnthonyChavezSource : A.AttributedSource
nmDPSAnthonyChavezSource = A.mkNoDOISource
  "New Mexico Department of Public Safety"
  "Anthony Chavez missing-person record"
  "New Mexico Missing Persons Clearinghouse"
  "2025"
  "https://www.dps.nm.gov/missing-persons/anthony-chavez/"
  A.governmentSource
  "primary missing-person identity/location/date carrier; does not pay LANL technical identity, quantum-physics work or cause of disappearance"
  A.publicAttribution

nmDPSStevenGarciaSource : A.AttributedSource
nmDPSStevenGarciaSource = A.mkNoDOISource
  "New Mexico Department of Public Safety"
  "Steven Abel Garcia missing-person record"
  "New Mexico Missing Persons Clearinghouse"
  "2025"
  "https://www.dps.nm.gov/missing-persons/steven-abel-garcia/"
  A.governmentSource
  "primary missing-person identity/location/date carrier; does not pay KCNSC duty scope, clearance, inventory anomaly or security-response claims"
  A.publicAttribution

nmDPSMcCaslandSource : A.AttributedSource
nmDPSMcCaslandSource = A.mkNoDOISource
  "New Mexico Department of Public Safety"
  "William Neil McCasland missing-person record"
  "New Mexico Missing Persons Clearinghouse"
  "2026"
  "https://www.dps.nm.gov/missing-persons/william-neil-mccasland/"
  A.governmentSource
  "primary missing-person identity/location/date carrier; does not pay a final-meeting, Space Force, UAP or programme-causation claim"
  A.publicAttribution

afrlMcCaslandSpaceForceHistoricalSource : A.AttributedSource
afrlMcCaslandSpaceForceHistoricalSource = A.mkNoDOISource
  "U.S. Air Force / AFRL; photo by Joanne Perkins"
  "210723-F-F3963-1001.JPG"
  "Air Force Research Laboratory photo gallery"
  "2021"
  "https://www.afrl.af.mil/News/Photos/igphoto/2002819872/"
  A.governmentSource
  "primary public carrier showing retired Maj. Gen. McCasland officiating a 2021 Kirtland ceremony inducting AFRL/SMC officers into the U.S. Space Force; this establishes historical institutional adjacency only and cannot pay a claimed February-2026 Space Force meeting"
  A.publicAttribution

kobNewMexicoClusterSource : A.AttributedSource
kobNewMexicoClusterSource = A.mkNoDOISource
  "KOB 4"
  "4 missing people with nuclear ties spark concern in New Mexico"
  "KOB 4"
  "2026"
  "https://www.kob.com/new-mexico/4-missing-persons-with-nuclear-ties-spark-concern-in-new-mexico/"
  A.newsSource
  "bounded secondary source for the four-case New Mexico aggregation and reported work-role context; its strongest defensible common coordinate is geography, not common cause"
  A.publicAttribution

kobCasiasResetSource : A.AttributedSource
kobCasiasResetSource = A.mkNoDOISource
  "Kassi Foote / KOB 4"
  "Family of Taos woman still looking for her a month after disappearance"
  "KOB 4"
  "2025"
  "https://www.kob.com/news/top-news/family-of-taos-woman-still-looking-for-her-a-month-after-disappearance/"
  A.newsSource
  "bounded secondary carrier for family-reported chronology, forgotten-badge account and factory-reset phone; does not independently prove who reset the device, when, why, or whether the reset was operationally significant"
  A.publicAttribution

kobCasiasFamilyInvestigationSource : A.AttributedSource
kobCasiasFamilyInvestigationSource = A.mkNoDOISource
  "KOB 4"
  "Family pushes for answers after Melissa Casias found dead in forest, hires lawyer to investigate"
  "KOB 4"
  "2026"
  "https://www.kob.com/news/top-news/family-pushes-for-answers-after-melissa-casias-found-dead-in-forest-hires-lawyer-to-investigate/"
  A.newsSource
  "bounded secondary carrier for family statements after recovery and the reported gun-near-remains context; family interpretation does not determine forensic manner"
  A.publicAttribution

laTimesCasiasAutopsySource : A.AttributedSource
laTimesCasiasAutopsySource = A.mkNoDOISource
  "Grace Toohey"
  "Inconclusive autopsy adds to mystery of Los Alamos lab worker found dead in remote forest"
  "Los Angeles Times"
  "2026"
  "https://www.latimes.com/world-nation/story/2026-08-18/unanswered-questions-continue-to-swirl-in-case-of-missing-new-mexico-los-alamos-lab-worker"
  A.newsSource
  "bounded secondary report quoting the New Mexico OMI result: gunshot wound to head, manner undetermined; the underlying autopsy remains the preferred primary forensic carrier"
  A.publicAttribution

laTimesCasiasRecoverySource : A.AttributedSource
laTimesCasiasRecoverySource = A.mkNoDOISource
  "Grace Toohey"
  "Missing worker at high-security lab in N.M. found dead in remote forest"
  "Los Angeles Times"
  "2026"
  "https://www.latimes.com/world-nation/story/2026-06-02/missing-worker-at-high-security-lab-in-n-m-found-dead-in-remote-forest"
  A.newsSource
  "bounded secondary recovery/event report; supports Taos-home context, LANL employment and recovery beside a handgun as reported, not manner or culprit"
  A.publicAttribution

foxLeBlancTelemetrySource : A.AttributedSource
foxLeBlancTelemetrySource = A.mkNoDOISource
  "Peter D'Abrosca / Fox News Digital"
  "NASA engineer died in fiery Alabama crash as FBI probes scientist deaths"
  "Fox News Digital"
  "2026"
  "https://www.foxnews.com/us/nasa-nuclear-engineer-found-dead-burned-tesla-vanishing-alabama-home-last-year/"
  A.newsSource
  "bounded secondary carrier for the reported Tesla/Sentry-derived approximately four-hour Huntsville airport stop, family account and crash chronology; raw Tesla/law-enforcement data remains required for event promotion"
  A.publicAttribution

laMagRezaSource : A.AttributedSource
laMagRezaSource = A.mkNoDOISource
  "Lauren Conlin"
  "Missing NASA Scientist Monica Reza: Geo-Profiler Suggests Possible Staged Disappearance"
  "Los Angeles Magazine"
  "2026"
  "https://lamag.com/crimeinla/missing-nasa-scientist-monica-reza-geo-profiler-suggests-possible-staged-disappearance/"
  A.newsSource
  "secondary investigative carrier for search chronology, recovered-beanie reporting and a profiler's staged-disappearance hypothesis; the hypothesis is not a primary event fact"
  A.publicAttribution

laMagRezaFamilySource : A.AttributedSource
laMagRezaFamilySource = A.mkNoDOISource
  "Lauren Conlin"
  "Exclusive: For Monica Reza's Family, It Doesn't Make Sense"
  "Los Angeles Magazine"
  "2026"
  "https://lamag.com/news/exclusive-for-monica-rezas-family-it-doesnt-make-sense/"
  A.newsSource
  "secondary family-interview carrier for event-time JPL role and search details; does not establish a classified programme, interception or common cause"
  A.publicAttribution

armyCoordinateDiscoverySource : A.AttributedSource
armyCoordinateDiscoverySource = A.mkNoDOISource
  "ZPEnergy community transcription / historical pointer"
  "Gravity-Waves & Missing Scientists at AmericanAntigravity.Com"
  "ZPEnergy"
  "historical web manifestation"
  "https://www.zpenergy.com/modules.php?file=print&name=News&sid=838"
  A.communitySource
  "discovery-only pointer for reported Army coordinate DAAH01-01-9-R001 and DoD FY2001 page-66 genealogy; cannot pay the award, amount, statement of work, classification or results until the original government carrier is inspected"
  A.publicAttribution

dodFY2001ArchivedLocatorSource : A.AttributedSource
dodFY2001ArchivedLocatorSource = A.mkNoDOISource
  "U.S. Department of Defense / archived locator"
  "Annual Report on Cooperative Agreements and Other Transactions Entered into During FY2001 Under 10 USC 2371"
  "archived acq.osd.mil FY01RPT.doc locator"
  "2001"
  "https://web.archive.org/web/20210801183915id_/https://www.acq.osd.mil/dpap/Docs/FY01RPT.doc"
  A.archivalSource
  "existence/custody locator for the reported original DoD carrier; the National Academies independently cites the same original FY01RPT.doc URL, but this atlas does not claim the archived bytes/page-66 row have been inspected in-session"
  A.existenceOnlyAttribution

investigativeSourceAtlas : A.AttributedSourceAtlas
investigativeSourceAtlas = A.mkSourceAtlas
  "missing/deceased scientists investigative source atlas"
  "DASHI.Culture.MissingDeceasedInvestigativeAttributedSourceAtlasExact"
  (nasaNingNCC8124Source ∷
   ningYBCO1997Source ∷
   rezaEarlyPatentSource ∷
   rezaPatentSource ∷
   nasaFusionDrivenRocketSource ∷
   nasaDirectFusionDriveSource ∷
   nasaAneutronicFusionSource ∷
   nasaQuantumVacuumMentionSource ∷
   houseOversightSource ∷
   nmDPSAnthonyChavezSource ∷
   nmDPSStevenGarciaSource ∷
   nmDPSMcCaslandSource ∷
   afrlMcCaslandSpaceForceHistoricalSource ∷
   kobNewMexicoClusterSource ∷
   kobCasiasResetSource ∷
   kobCasiasFamilyInvestigationSource ∷
   laTimesCasiasAutopsySource ∷
   laTimesCasiasRecoverySource ∷
   foxLeBlancTelemetrySource ∷
   laMagRezaSource ∷
   laMagRezaFamilySource ∷
   armyCoordinateDiscoverySource ∷
   dodFY2001ArchivedLocatorSource ∷ [])
  "Attribution/snowball spine for primary, bounded-secondary, archival-locator and discovery-only sources used by the investigative Pareto; formalisationRelationship on each entry states the exact proposition boundary."

sourceAtlasDoesNotPromoteClaims :
  A.atlasCreatesAuthority investigativeSourceAtlas ≡ false
sourceAtlasDoesNotPromoteClaims = refl

record InvestigativeAttributionBoundary : Set where
  constructor investigative-attribution-boundary
  field
    newsSourceMayNominateAcquisition : Bool
    discoverySourceMayPayPrimaryAward : Bool
    archivalLocatorEqualsInspectedCarrier : Bool
    sourceRepetitionMayCreateSameObject : Bool
    sourceLinkMayCreateForensicCause : Bool
    primaryCarrierStillPreferredWhenRecoverable : Bool

canonicalInvestigativeAttributionBoundary : InvestigativeAttributionBoundary
canonicalInvestigativeAttributionBoundary =
  investigative-attribution-boundary true false false false false true
