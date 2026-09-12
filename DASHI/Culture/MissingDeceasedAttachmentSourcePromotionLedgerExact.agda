module DASHI.Culture.MissingDeceasedAttachmentSourcePromotionLedgerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as A

------------------------------------------------------------------------
-- ATTACHMENT SOURCE-PROMOTION LEDGER
--
-- Claim -> named manifestation -> desired primary carrier -> exact proposition
-- -> promotion boundary.  Discovery links are retained even when they are not
-- yet evidence-bearing.
------------------------------------------------------------------------

data PromotionState : Set where
  discoveryOnly
  boundedSecondary
  primaryLocatedUninspected
  primaryInspected
  pruned : PromotionState

record SourcePromotionRow : Set where
  constructor source-promotion-row
  field
    label : String
    attachmentPages : String
    attachmentClaim : String
    namedManifestation : String
    currentState : PromotionState
    desiredPrimaryCarrier : String
    exactPropositionNeeded : String
    promotionBoundary : String

open SourcePromotionRow public

palantirAIPConClaim : SourcePromotionRow
palantirAIPConClaim = source-promotion-row
  "Palantir/AIPCon alien-antigravity-machine remark"
  "44-46"
  "an unnamed U.S. general allegedly asked Palantir to build software for an 'alien anti-gravity machine'"
  "Cybernews/search capture referencing Alex Karp at AIPCon 11"
  boundedSecondary
  "full AIPCon 11 video/transcript or Palantir-hosted event record"
  "exact speaker, wording, date, context and whether statement described an actual programme, anecdote, joke or hypothetical"
  "even exact wording would not establish an operational antigravity machine without same-object programme and apparatus evidence"

trinityClathrateQuasicrystalClaim : SourcePromotionRow
trinityClathrateQuasicrystalClaim = source-promotion-row
  "Trinity clathrate/quasicrystal"
  "41-43"
  "extreme Trinity-test material formation is used as a comparator for unusual crystal phases"
  "ResearchGate/search capture"
  discoveryOnly
  "original peer-reviewed crystallography papers and specimen provenance"
  "composition, phase identity, formation context and whether clathrate/quasicrystal are from the same specimen/event"
  "terrestrial extreme-material formation cannot promote to recovered anomalous technology or a missing-scientist cause"

anomalousWaferClaim : SourcePromotionRow
anomalousWaferClaim = source-promotion-row
  "20x10 mm multidomain ultra-pure wafer"
  "42-43"
  "an alleged leaked/declassified anomalous crystal wafer is claimed to exceed ordinary synthesis limits"
  "Medium/ResearchGate/search capture"
  discoveryOnly
  "original declassified document, dataset, specimen record or laboratory report"
  "actual dimensions, composition, purity, provenance, manufacturing comparison and custody"
  "absence of a primary carrier means the wafer remains a discovery claim; it cannot be used to infer Maiwald deployment or NHI provenance"

projectAnchorClaim : SourcePromotionRow
projectAnchorClaim = source-promotion-row
  "Project Anchor gravity-loss hoax"
  "44-45"
  "viral claim that Earth would lose gravity for seven seconds is reinterpreted as deliberate data poisoning"
  "NewsNation/New York Post/IFLScience-style coverage and NASA denial referenced in capture"
  boundedSecondary
  "original viral provenance plus NASA primary denial and any evidence of coordinated sponsorship/distribution"
  "who originated/amplified the claim and whether any state/contractor actor intentionally seeded it"
  "a false viral claim plus an official denial does not establish an information operation"

quantumRepulsionClaim : SourcePromotionRow
quantumRepulsionClaim = source-promotion-row
  "2026 effective gravitational repulsion"
  "45-46"
  "quantum superposition is claimed to produce measurable effective repulsion"
  "YouTube/science-news/search capture"
  discoveryOnly
  "original 2026 paper/preprint and experimental or proposed measurement record"
  "Hamiltonian, source/probe masses, prepared state, observable, magnitude and whether result is theoretical or experimental"
  "effective/conditional repulsion does not promote to new fundamental antigravity or aerospace propulsion"

timeCrystalClaim : SourcePromotionRow
timeCrystalClaim = source-promotion-row
  "2026 time/spacetime crystal claims"
  "47-48"
  "macroscopic room-temperature time-crystal and alleged spacetime-crystal/black-hole results are combined into a propulsion story"
  "NYU/ScienceDaily/Phys.org/search capture"
  discoveryOnly
  "original papers/preprints for each distinct result"
  "system, symmetry, non-reciprocity, energy accounting, spacetime model and any actual gravitational observable"
  "time-crystal behaviour does not by itself imply metric engineering or propulsion"

qetClaim : SourcePromotionRow
qetClaim = source-promotion-row
  "Quantum Energy Teleportation"
  "49-51"
  "QET is described as harvesting usable energy directly from zero-point vacuum and then scaled to thrust"
  "Quanta/PTEP/Medium/search capture"
  discoveryOnly
  "original QET theory and experimental papers"
  "complete local/global energy accounting, measurement/feed-forward cost, extracted energy and experimental observable"
  "QET does not promote to net free-energy extraction, infinite fuel, vacuum thrust or a missing-scientist programme"

wormholeSimulationClaim : SourcePromotionRow
wormholeSimulationClaim = source-promotion-row
  "ER=EPR / holographic wormhole simulation"
  "52-54"
  "quantum-processor model dynamics are reinterpreted as literal traversable-spacetime engineering"
  "Google Research/arXiv/APS/search capture"
  discoveryOnly
  "primary Nature/arXiv/Google research paper and model code/experimental record"
  "what was simulated, what observable matched the gravitational model and what was not a literal spacetime measurement"
  "simulation/duality correspondence cannot promote to a macroscopic physical wormhole"

spaceForceMeetingClaim : SourcePromotionRow
spaceForceMeetingClaim = source-promotion-row
  "McCasland February-2026 Space Force meeting"
  "29, 33"
  "bodycam/surveillance allegedly shows a Space Force meeting days before disappearance"
  "NewsNation/social/search capture"
  discoveryOnly
  "authenticated bodycam/surveillance/log entry plus agency/person identities"
  "date, attendees, purpose and whether the encounter is the same claimed meeting"
  "historical McCasland-Space-Force adjacency cannot substitute for event-time meeting evidence"

chavezPoliceStatementClaim : SourcePromotionRow
chavezPoliceStatementClaim = source-promotion-row
  "Chavez matter-in-two-places police statement"
  "18-19, 24"
  "a friend allegedly told police Chavez was discussing how matter can exist in two places at once"
  "journalistic references to police report"
  boundedSecondary
  "actual police-report page/interview supplement"
  "speaker identity, exact wording, date, context and whether any scientific collaborator/project is identified"
  "a reported statement cannot weld Chavez to a quantum-teleportation programme or explain disappearance"

casiasDeviceResetClaim : SourcePromotionRow
casiasDeviceResetClaim = source-promotion-row
  "Casias factory-reset devices"
  "19, 24, 28, 32"
  "personal devices were reportedly factory reset before/around disappearance"
  "family-reported through KOB and later news synthesis"
  boundedSecondary
  "device forensic extraction/logs, warrant return or police digital-forensics report"
  "device identity, reset timestamp, reset mechanism/account/IP if recoverable and examiner provenance"
  "family/news report cannot identify who reset devices or why"

leblancTelemetryClaim : SourcePromotionRow
leblancTelemetryClaim = source-promotion-row
  "LeBlanc Tesla airport staging interval"
  "16, 32"
  "vehicle allegedly remained at Huntsville airport for roughly four hours before fatal route"
  "Fox/KLFY/news synthesis"
  boundedSecondary
  "raw Tesla cloud/vehicle telemetry and law-enforcement extraction"
  "timestamped location series, Sentry availability, access events and provenance"
  "reported interval does not itself establish interception, staging or common cause"

armyOTAClaim : SourcePromotionRow
armyOTAClaim = source-promotion-row
  "DAAH01-01-9-R001 Army/AC Gravity coordinate"
  "59-70"
  "reported FY2001 Other Transaction for a Gravito-Electro Magnetic Superconductivity Experiment"
  "ZPEnergy transcription plus archived FY01RPT.doc locator"
  primaryLocatedUninspected
  "archived/original DoD FY2001 annual-report row, then Army AMCOM agreement/SOW and closeout"
  "exact awardee, amount, title, agreement identifier, authority, dates, distribution/classification and technical outcome"
  "archive locator or predicted metadata cannot pay the award row until inspected; missing closeout does not imply suppression"

mondaloySingleCrystalClaim : SourcePromotionRow
mondaloySingleCrystalClaim = source-promotion-row
  "Mondaloy single-crystal equivalence"
  "35-40, 61-70"
  "the attachment repeatedly slides from the Reza alloy into generic single-crystal-superalloy language"
  "patent plus generalized materials-search synthesis"
  boundedSecondary
  "same-object patent/process/crystallography or manufacturing record"
  "whether the Reza/Mondaloy article is directionally solidified single crystal versus polycrystalline/grain-boundary-engineered alloy"
  "gamma/gamma-prime microstructure and grain-boundary strengthening do not establish a single-crystal article"

sourcePromotionLedger : List SourcePromotionRow
sourcePromotionLedger =
  palantirAIPConClaim ∷ trinityClathrateQuasicrystalClaim ∷ anomalousWaferClaim ∷
  projectAnchorClaim ∷ quantumRepulsionClaim ∷ timeCrystalClaim ∷ qetClaim ∷
  wormholeSimulationClaim ∷ spaceForceMeetingClaim ∷ chavezPoliceStatementClaim ∷
  casiasDeviceResetClaim ∷ leblancTelemetryClaim ∷ armyOTAClaim ∷
  mondaloySingleCrystalClaim ∷ []

missingPrimaryCarrierDoesNotProveSuppression : Bool
missingPrimaryCarrierDoesNotProveSuppression = true

mediaHoaxDoesNotProveDisinformationOperation : Bool
mediaHoaxDoesNotProveDisinformationOperation = true

primaryScienceDoesNotPaySpeculativeScaleUp : Bool
primaryScienceDoesNotPaySpeculativeScaleUp = true
