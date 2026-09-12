module DASHI.Culture.MissingDeceasedFullAttachmentClaimAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- FULL 71-PAGE ATTACHMENT CLAIM ATLAS
--
-- This owner is an accounting surface, not an evidence authority.  It records
-- each materially distinct claim family in the supplied 71-page capture and
-- routes it to the existing science/attribution/Pareto machinery.  A row may
-- preserve a useful discovery lead even when its source class is weak.
------------------------------------------------------------------------

data AttachmentClaimClass : Set where
  maiwaldPublicScience
  rosterAndArea51Narrative
  engineeringStackConvergence
  nonScientistOperationalSweep
  southwestGeography
  reportedForensicAnomaly
  evidentiaryGap
  oxygenRichAlloy
  singleCrystalMetamaterialConflation
  anomalousMaterialSample
  informationPoisoning
  effectiveGravityRepulsion
  timeCrystalPropulsion
  qetScaleUp
  wormholeScaleUp
  disclosureAssetConsolidation
  counterEspionageSweep
  armyCommercialTransfer
  congressionalHoneyPot
  archivePrediction : AttachmentClaimClass

record AttachmentClaim : Set where
  constructor attachment-claim
  field
    pageRange : String
    claimClass : AttachmentClaimClass
    personOrObject : String
    attachmentClaim : String
    namedManifestation : String
    currentSourceClass : String
    paidKernel : String
    unpaidBridge : String
    ordinaryOrControlExplanation : String
    exactAcquisition : String
    alreadyOwnedElsewhere : Bool

open AttachmentClaim public

pages01to05Maiwald : AttachmentClaim
pages01to05Maiwald = attachment-claim
  "1-5"
  maiwaldPublicScience
  "Frank Maiwald / JPL SURP action spectroscopy"
  "messenger photodissociation action spectroscopy disambiguates molecular isomers and is later pulled into the missing-scientist narrative"
  "JPL SURP poster/index plus synthesized Google-search capture"
  "primary project science mixed with search synthesis"
  "JPL project identity, PI/co-I surface, cryogenic ion-trap/messenger spectroscopy capability"
  "no classified Area-51/NHI deployment or causal event bridge"
  "ordinary planetary/astrobiology analytical chemistry"
  "JPL project manifestations, instrument deployment logs, sample/data custody and exact post-2023 handover"
  true

pages06to11Roster : AttachmentClaim
pages06to11Roster = attachment-claim
  "6-11"
  rosterAndArea51Narrative
  "U.S. missing/deceased roster"
  "heterogeneous scientists/engineers/defense-linked people are aggregated into an Area-51/UAP narrative"
  "House inquiry, news packages, Wikipedia/search surfaces"
  "government inquiry plus bounded secondary aggregation"
  "public inquiry exists and individual event/work identities can be sourced separately"
  "aggregation does not establish a shared programme, culprit, motive or UAP cause"
  "large technical workforces generate heterogeneous adverse events; media selection can induce apparent clustering"
  "scope-specific roster, primary event carriers, matched controls and common-programme receipts"
  true

pages12to17EngineeringStack : AttachmentClaim
pages12to17EngineeringStack = attachment-claim
  "12-17"
  engineeringStackConvergence
  "McCasland + Reza + Amy + Maiwald + LeBlanc"
  "real technical portfolios are re-read as one reverse-engineering/propulsion stack"
  "alternative/UAP commentary in the attachment"
  "speculative/community synthesis"
  "individual domain kernels are real: aerospace leadership, oxygen-rich alloy, exotic-gravity reverse-search, spectroscopy and NTP instrumentation"
  "no same-programme architecture, handoff, common apparatus or causal event object"
  "independent advanced programmes can be technically adjacent without forming one engineered system"
  "programme/contract/custody objects naming at least two stack components on the same object and dated before the events"
  false

pages18to20NonScientists : AttachmentClaim
pages18to20NonScientists = attachment-claim
  "18-20"
  nonScientistOperationalSweep
  "Anthony Chavez + Melissa Casias + Steven Garcia"
  "support/logistics personnel are claimed to complete an operational cleanup rather than weaken the theory"
  "news reports plus Reddit/4chan/UFO commentary"
  "bounded secondary + speculative community"
  "role-capability distinctions make facilities, routing and inventory visibility legitimate acquisition coordinates"
  "job title does not prove clearance scope, programme knowledge or common operational action"
  "large secure institutions necessarily employ many support roles"
  "dated duty/access/custody records and matched same-role controls"
  true

pages21to30Southwest : AttachmentClaim
pages21to30Southwest = attachment-claim
  "21-30"
  southwestGeography
  "LANL / Albuquerque-Kirtland / Reza western vector"
  "events are framed as a Southwest Tech Corridor and then interpreted through competing counter-intelligence/UAP lenses"
  "NM DPS, regional journalism and speculative synthesis"
  "primary locations + bounded secondary clustering"
  "a real New Mexico aggregation exists at event/person level"
  "White Sands/common-facility/common-cause edge remains unpaid"
  "defense-lab workforce density can produce geographic clustering"
  "primary event coordinates, workplace/programme objects and matched geographic denominator"
  true

pages31to34Gaps : AttachmentClaim
pages31to34Gaps = attachment-claim
  "31-34"
  evidentiaryGap
  "Casias / LeBlanc / McCasland / role controls"
  "device reset, Tesla telemetry, claimed Space Force meeting and shared-access controls are proposed as decisive gaps"
  "KOB/Fox/NewsNation-style reporting summarized in attachment"
  "bounded secondary/discovery"
  "reported anomalies can nominate exact primary carriers"
  "raw device/vehicle/bodycam/meeting/access records are not supplied by the attachment"
  "reported anomaly may be mundane, misdescribed or selection-amplified"
  "forensic extraction logs; Tesla/cloud logs; authenticated meeting/tasking records; access-control objects"
  true

pages35to40Materials : AttachmentClaim
pages35to40Materials = attachment-claim
  "35-40"
  oxygenRichAlloy
  "Reza/Jacinto/Hardwick alloy + generic SX/THz material discussion"
  "oxygen-rich burn-resistant high-strength Ni alloy is expanded into single-crystal and THz-metamaterial comparisons"
  "patent family mixed with general materials articles and speculative commentary"
  "primary patent kernel + secondary/general comparison"
  "composition/process, gamma/gamma-prime strengthening and high-pressure oxygen test environment are source-backed"
  "the Reza object is not thereby a directionally solidified single crystal, THz metamaterial or gravity waveguide"
  "distinct terrestrial material classes explain the compared properties"
  "same-object crystallography/processing receipt for any stronger classification"
  true

pages41to43AnomalousMaterial : AttachmentClaim
pages41to43AnomalousMaterial = attachment-claim
  "41-43"
  anomalousMaterialSample
  "Trinity clathrate/quasicrystal + alleged multidomain ultra-pure wafers"
  "real extreme-material crystallography is blended with an alleged leaked anomalous-wafer object and Maiwald diagnostic claims"
  "ResearchGate/Medium/search synthesis in attachment"
  "mixed academic discovery and weak discovery-only manifestations"
  "Trinity-related quasicrystal/clathrate work may be a real science comparator"
  "the alleged 20x10 mm recovered wafer, energy-shield role and Maiwald same-sample use are not paid"
  "nonequilibrium/extreme synthesis can produce unusual terrestrial phases"
  "original paper/dataset for each material plus chain-of-custody and actual analytical method used"
  false

pages44to46InfoOpsGravity : AttachmentClaim
pages44to46InfoOpsGravity = attachment-claim
  "44-46"
  informationPoisoning
  "Palantir AIPCon / Project Anchor / quantum-gravity repulsion"
  "public remarks, a viral gravity hoax and a recent effective-repulsion claim are interpreted as a disclosure/noise-management frontier"
  "Cybernews/news/YouTube/search synthesis"
  "mixed journalism, viral claim and science-popularization"
  "individual public remarks/hoax debunks/academic results may be independently sourceable"
  "no evidence yet that the hoax was an intentional state data-poisoning operation or that effective repulsion is an aerospace device"
  "viral misinformation and unrelated frontier research can co-occur without coordination"
  "AIPCon transcript/video; original NASA denial; primary gravity paper and experiment details"
  false

pages47to48TimeCrystal : AttachmentClaim
pages47to48TimeCrystal = attachment-claim
  "47-48"
  timeCrystalPropulsion
  "time crystals / non-reciprocal acoustic matter / alleged spacetime-crystal black-hole transition"
  "time-crystal research is scaled into a gravitational propulsion architecture"
  "NYU/ScienceDaily/Phys.org/YouTube/search synthesis"
  "academic-popularization mixed with speculative extrapolation"
  "time-translation symmetry breaking and non-reciprocal dynamics are legitimate research topics"
  "no same-object proof of metric engineering, black-hole engine or propulsion"
  "novel nonequilibrium dynamics do not imply gravitational control"
  "exact DOI/arXiv objects, model assumptions, experiment observables and any claimed propulsion coupling"
  false

pages49to51QET : AttachmentClaim
pages49to51QET = attachment-claim
  "49-51"
  qetScaleUp
  "quantum energy teleportation / zero-point framing"
  "QET is described as usable vacuum-energy extraction and then scaled to macroscopic thrust/field propulsion"
  "Quanta/PTEP/Medium/social/search synthesis"
  "academic concept mixed with over-strong interpretation"
  "QET protocols can transfer/extract bounded energy conditioned on measurements in entangled systems"
  "QET does not establish net free vacuum-energy extraction, infinite fuel or aerospace thrust"
  "information/energy accounting and laboratory-scale protocols explain the published effect"
  "primary QET paper, complete energy budget, scaling law and independent thrust/gravity observable"
  false

pages52to54Wormhole : AttachmentClaim
pages52to54Wormhole = attachment-claim
  "52-54"
  wormholeScaleUp
  "ER=EPR / holographic teleportation / size winding / counterportation"
  "quantum-information simulations are reinterpreted as physical traversable-spacetime technology"
  "APS/arXiv/Google Research/Phys.org/search synthesis"
  "primary theory/experiment mixed with speculative scale-up"
  "ER=EPR and holographic-wormhole simulation are legitimate theory/simulation objects"
  "simulation/analogy does not create a literal macroscopic traversable wormhole"
  "quantum processor dynamics can emulate a model without engineering spacetime"
  "primary papers, exact simulator/model correspondence and any independent spacetime observable"
  false

pages55to60MasterTheories : AttachmentClaim
pages55to60MasterTheories = attachment-claim
  "55-60"
  disclosureAssetConsolidation
  "asset consolidation / breakthrough horizon / clean sweep"
  "three master theories explain the roster as relocation, breakthrough capture or counter-espionage response"
  "community narrative summarized by search output"
  "speculative synthesis"
  "the theories generate potentially discriminating acquisition targets"
  "none is paid by technical adjacency, event heterogeneity or inquiry existence"
  "ordinary succession, workforce base rates, crime/accident/illness and media aggregation remain controls"
  "pre-event common tasking, same-programme custody, actor-specific action and matched-control divergence"
  false

pages61to65NingCore : AttachmentClaim
pages61to65NingCore = attachment-claim
  "61-65"
  armyCommercialTransfer
  "Ning Li / NASA NCC8-124 / reported Army DAAH01-01-9-R001"
  "a historical theory-experiment-programme sequence is used as foundation for a later hidden technology-transfer narrative"
  "APS/Physica C/NASA NTRS plus secondary Army-coordinate transcription"
  "primary academic/government kernel + archival/discovery residual"
  "Li/Torr theory, 1997 static constraint and NASA NCC8-124 incomplete programme are paid"
  "Army award row, SOW, outcome, apparatus continuity and commercial transfer remain unpaid until primary carrier inspection"
  "a follow-on procurement can exist without successful anomalous physics or covert monopoly"
  "inspect archived FY01RPT row; acquire Army SOW/closeout, AC Gravity registry and apparatus lineage"
  true

pages66to70ContractClaims : AttachmentClaim
pages66to70ContractClaims = attachment-claim
  "66-70"
  congressionalHoneyPot
  "AC Gravity IP hijack / Mondaloy grid / House honey-pot / predictive AMCOM metadata"
  "community theories assert successful IP transfer, containment use, congressional trapping and a predicted restricted DTIC closeout"
  "community/search synthesis plus hypothetical code"
  "discovery-only / predicted model"
  "the reported agreement identifier is a valid acquisition key; Mondaloy composition is independently source-backed"
  "predicted report designation, DistB/ITAR status, hidden AD number, IP hijack and honey-pot purpose are not evidence"
  "ordinary OTA reporting heterogeneity and speculative model construction can produce the same apparent gaps"
  "same-era AMCOM controls and the actual award/report/DTIC carrier before assigning anomaly status"
  false

page71Terminal : AttachmentClaim
page71Terminal = attachment-claim
  "71"
  archivePrediction
  "attachment terminal page"
  "no additional substantive claim beyond the preceding search capture"
  "Google-search capture footer"
  "non-evidentiary manifestation"
  "page accounted for"
  "none"
  "none"
  "none"
  false

fullAttachmentClaimAtlas : List AttachmentClaim
fullAttachmentClaimAtlas =
  pages01to05Maiwald ∷ pages06to11Roster ∷ pages12to17EngineeringStack ∷
  pages18to20NonScientists ∷ pages21to30Southwest ∷ pages31to34Gaps ∷
  pages35to40Materials ∷ pages41to43AnomalousMaterial ∷ pages44to46InfoOpsGravity ∷
  pages47to48TimeCrystal ∷ pages49to51QET ∷ pages52to54Wormhole ∷
  pages55to60MasterTheories ∷ pages61to65NingCore ∷ pages66to70ContractClaims ∷
  page71Terminal ∷ []

attachmentPages1Through71AccountedFor : Bool
attachmentPages1Through71AccountedFor = true

singleCrystalMondaloyEquivalencePaid : Bool
singleCrystalMondaloyEquivalencePaid = false

technicalAdjacencyCreatesSameProgramme : Bool
technicalAdjacencyCreatesSameProgramme = false

attachmentSourceRepetitionCreatesAuthority : Bool
attachmentSourceRepetitionCreatesAuthority = false
