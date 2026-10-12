module DASHI.Cognition.EpsteinGlobalSciencePatronageRouterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinPsychedelicParetoSnowballExact as Psychedelic
import DASHI.Cognition.ChomskyEpsteinRelationshipExact as Chomsky
import DASHI.Cognition.EpsteinSciencePatronageMicrocosmExact as Patronage
import DASHI.Cognition.EpsteinNaturePublishingBoundaryExact as Publishing
import DASHI.Cognition.EpsteinGlobalHighProfileWebReceiptsExact as Web
import DASHI.Cognition.EpsteinPublicSourceScienceNetworkAtlasExact as PublicAtlas

------------------------------------------------------------------------
-- GLOBAL EPSTEIN SCIENCE / PATRONAGE ACQUISITION ROUTER
--
-- Corrects local-lane and famous-person over-indexing. Fresh public-source
-- acquisition shows that several important objects are infrastructures rather
-- than individuals: Edge/Brockman salons, Harvard PED, MIT Media Lab, ASU
-- Origins, Seed science media, TerraMar and the historical Pergamon publishing
-- genealogy. Each acquisition round must begin with a fresh public-source sweep
-- before allocating corpus effort.
--
-- Shares below are search-allocation heuristics, not truth, culpability,
-- wrongdoing, scientific-authority or relationship-strength scores.
------------------------------------------------------------------------

data GlobalLane : Set where
  yuConsciousnessPsychedelics : GlobalLane
  chomskyLanguageBrokerage : GlobalLane
  gatesFoundationPhilanthropy : GlobalLane
  harvardNowakChurchPED : GlobalLane
  mitMediaLabInstitutional : GlobalLane
  kraussASUOrigins : GlobalLane
  brockmanEdgeBrokerage : GlobalLane
  seedScienceMedia : GlobalLane
  santaFeGellMann : GlobalLane
  maxwellTerraMarNonprofit : GlobalLane
  maxwellPergamonElsevierPublishing : GlobalLane
  doblinMAPSInstitutionalisation : GlobalLane
  hearstPSFCFundingChronology : GlobalLane
  broaderScientistAtlasExpansion : GlobalLane

record GlobalLaneStatus : Set where
  constructor global-lane-status
  field
    lane : GlobalLane
    directOrInstitutionalRelationEstablished : Bool
    primaryCorpusSaturationOpen : Bool
    crossDomainBridgePotential : Bool
    requiresIndependentEdgeReceiptForNewClaims : Bool
    note : String
open GlobalLaneStatus public

yuStatus : GlobalLaneStatus
yuStatus = global-lane-status yuConsciousnessPsychedelics true true true true
  "Dense direct funding/brokerage/altered-state seam; local exploitation leader, not global default."

chomskyStatus : GlobalLaneStatus
chomskyStatus = global-lane-status chomskyLanguageBrokerage true true true true
  "Direct repeated relationship paid; acquire functional role, adjacent introductions/projects and independent one-hop expansion."

gatesStatus : GlobalLaneStatus
gatesStatus = global-lane-status gatesFoundationPhilanthropy true true true true
  "Foundation review establishes 2011-2014 engagement around a proposed public-health DAF and Epstein's IPI introduction; saturate meeting-by-meeting and adjacent philanthropy topology."

harvardStatus : GlobalLaneStatus
harvardStatus = global-lane-status harvardNowakChurchPED true true true true
  "Harvard's own review establishes USD 9.179m giving, USD 6.5m to create PED, >40 PED visits after prison, and donor introductions later yielding USD 7.5m to Nowak and USD 2m to Church without establishing that those donor funds came from Epstein."

mitStatus : GlobalLaneStatus
mitStatus = global-lane-status mitMediaLabInstitutional true true true true
  "MIT fact-finding establishes 10 Epstein gifts totaling USD 850k, repeated campus visits and post-conviction donation handling. Expand researcher/donor/broker topology rather than re-proving institutional contact."

kraussStatus : GlobalLaneStatus
kraussStatus = global-lane-status kraussASUOrigins true true true true
  "Public-record reporting establishes post-conviction Epstein/Origins funding and a larger Leon/Debra Black donation lane. Acquire all EFTA correspondence, events, speaker lists, board proposals, uses of funds and donor-introduction paths."

brockmanStatus : GlobalLaneStatus
brockmanStatus = global-lane-status brockmanEdgeBrokerage true true true true
  "High-quality reporting identifies Brockman/Edge as an entree and convening infrastructure linking Epstein to scientists and technology elites. Saturate Edge funding, dinners, invitations, flights, introductions and client graph."

seedStatus : GlobalLaneStatus
seedStatus = global-lane-status seedScienceMedia false true true true
  "Reporting places Ghislaine Maxwell and possibly Epstein in Seed Media's science-media governance orbit. Resolve exact corporate records, board roles, investments and editorial/business interfaces before promoting control or influence."

santaFeStatus : GlobalLaneStatus
santaFeStatus = global-lane-status santaFeGellMann true true true true
  "Gell-Mann acknowledged Epstein financial support; a 2025 DOJ interview records Ghislaine Maxwell stating she introduced Epstein to Gell-Mann through a pre-existing Maxwell/Santa Fe connection. Witness statement and independent receipts remain separately typed."

terramarStatus : GlobalLaneStatus
terramarStatus = global-lane-status maxwellTerraMarNonprofit true true true true
  "US v Maxwell exhibit establishes a USD 57k Epstein Interests Foundation donation to Ghislaine Maxwell-founded TerraMar. Expand nonprofit, donor, event and institutional edges separately from publishing genealogy."

maxwellPublishingStatus : GlobalLaneStatus
maxwellPublishingStatus = global-lane-status maxwellPergamonElsevierPublishing true true true true
  "Robert Maxwell->Pergamon->Elsevier is a major historical scientific-publishing and scientist-networking lineage; acquisition must now test specific continuity/advance-knowledge/access/influence claims rather than treating the lane as genealogy only."

doblinStatus : GlobalLaneStatus
doblinStatus = global-lane-status doblinMAPSInstitutionalisation false true true true
  "Resolve proposed invite versus actual correspondence, meeting, funding or institutional overlap."

hearstStatus : GlobalLaneStatus
hearstStatus = global-lane-status hearstPSFCFundingChronology false true true true
  "Resolve Epstein/Hearst primary records against PSFC/MAPS chronology without importing causation from timing."

atlasStatus : GlobalLaneStatus
atlasStatus = global-lane-status broaderScientistAtlasExpansion false true true true
  "Fresh public-source/corpus atlases nominate Trivers, Hillis, Lloyd, Boyden, Church, Minsky, Gell-Mann and other scientists; each nominated lane must resolve back to primary/institutional/reliable reporting before promotion."

------------------------------------------------------------------------
-- Search-led exploit/explore portfolio.
--
-- The exact shares are provisional. More important than the values is the rule:
-- no next Pareto round may reuse them without a fresh web/institutional-source
-- sweep and a marginal-gain recomputation.
------------------------------------------------------------------------

data AcquisitionMode : Set where
  exploit : AcquisitionMode
  expandPaidHub : AcquisitionMode
  infrastructureAudit : AcquisitionMode
  sourceAtlasExplore : AcquisitionMode
  falsificationProbe : AcquisitionMode

record GlobalAcquisitionInstruction : Set where
  constructor global-acquisition-instruction
  field
    target : GlobalLane
    mode : AcquisitionMode
    relativeShare : Nat
    stopWhenMarginalRedundancyRises : Bool
    requireEdgeLocalProvenance : Bool
    freshPublicSourceSweepBeforeNextRound : Bool
    instruction : String
open GlobalAcquisitionInstruction public

currentGlobalAcquisitionPlan : List GlobalAcquisitionInstruction
currentGlobalAcquisitionPlan =
  global-acquisition-instruction yuConsciousnessPsychedelics exploit 15 true true true
    "Continue Yu whole-thread/attachment/entity saturation, capped so corpus density cannot monopolise acquisition."
  ∷ global-acquisition-instruction brockmanEdgeBrokerage infrastructureAudit 15 true true true
    "Audit Edge as brokerage infrastructure: donations, dinners, invite/attendance distinction, flights, scientist introductions, clients and adjacent funders."
  ∷ global-acquisition-instruction harvardNowakChurchPED expandPaidHub 10 true true true
    "Expand Harvard PED/Nowak/Church through exact gifts, visits, introduced donors, grant applications, scientist meetings and governance records."
  ∷ global-acquisition-instruction kraussASUOrigins expandPaidHub 10 true true true
    "Acquire Krauss/Origins EFTA and ASU records around Epstein/Black funding, publicity acknowledgement, board/event proposals, introductions and exact use-of-funds."
  ∷ global-acquisition-instruction mitMediaLabInstitutional expandPaidHub 10 true true true
    "Expand MIT through donation destinations, Ito/Lloyd/Minsky contacts, visits, claimed coordinated donations and visibility/governance handling."
  ∷ global-acquisition-instruction gatesFoundationPhilanthropy expandPaidHub 10 true true true
    "Acquire Gates/Foundation meeting-by-meeting records, proposed DAF structure, IPI path and adjacent brokers/donors."
  ∷ global-acquisition-instruction santaFeGellMann expandPaidHub 5 true true true
    "Resolve Gell-Mann/Santa Fe funding and introduction lineage from independent records, keeping Ghislaine's witness statement separately typed."
  ∷ global-acquisition-instruction seedScienceMedia infrastructureAudit 5 true true true
    "Resolve Seed Media board/cap-table/investment/editorial records and any Epstein/Ghislaine access or influence; reporting is locator until corporate records pay the edge."
  ∷ global-acquisition-instruction maxwellTerraMarNonprofit expandPaidHub 5 true true true
    "Expand the paid Epstein Foundation->TerraMar edge through donors, events, institutional partners and science/policy networks."
  ∷ global-acquisition-instruction maxwellPergamonElsevierPublishing infrastructureAudit 5 true true true
    "Audit Maxwell/Pergamon/Elsevier scientist networking, attempted Elsevier stake/control, acquisition transition, editorial access and any later continuity claims; distinguish historical system influence from Epstein-era coordination."
  ∷ global-acquisition-instruction broaderScientistAtlasExpansion sourceAtlasExplore 5 true true true
    "Use broad 2026 scientist indexes only to nominate new high-yield names, then resolve every candidate to EFTA, institutional review or reliable reporting before admission."
  ∷ global-acquisition-instruction chomskyLanguageBrokerage expandPaidHub 5 true true true
    "Expand Chomsky one hop through introductions, projects, payments, travel/social contacts and adjacent academics."
  ∷ []

------------------------------------------------------------------------
-- Layered graph discipline.
------------------------------------------------------------------------

data NetworkLayer : Set where
  peopleLayer : NetworkLayer
  institutionLayer : NetworkLayer
  moneyLayer : NetworkLayer
  introductionLayer : NetworkLayer
  conveningLayer : NetworkLayer
  publishingLayer : NetworkLayer
  mediaLayer : NetworkLayer
  nonprofitLayer : NetworkLayer
  scienceTopicLayer : NetworkLayer
  governanceLayer : NetworkLayer

data EdgeStatus : Set where
  locatorOnly : EdgeStatus
  sourceObserved : EdgeStatus
  witnessStatement : EdgeStatus
  institutionalReviewEstablished : EdgeStatus
  independentlyCorroborated : EdgeStatus
  unresolvedSameObject : EdgeStatus

record LayeredEdgeDescriptor : Set where
  constructor layered-edge-descriptor
  field
    fromLabel toLabel : String
    layer : NetworkLayer
    relationLabel : String
    sourceIdentity : String
    status : EdgeStatus
    wrongdoingInferred : Bool
open LayeredEdgeDescriptor public

------------------------------------------------------------------------
-- Cross-owner availability receipts.
------------------------------------------------------------------------

chomskyDirectRelationshipAlreadyPaid :
  Chomsky.directRelationshipEstablished
    Chomsky.canonicalChomskyEpsteinRelationshipBoundary ≡ true
chomskyDirectRelationshipAlreadyPaid = refl

yuMicrocosmDoesNotRepresentWholeNetwork :
  Patronage.representsWholeScienceNetwork Patronage.yuPsychedelicMicrocosm ≡ false
yuMicrocosmDoesNotRepresentWholeNetwork = refl

gatesRepeatedEngagementAlreadyPaid :
  Web.repeatedEngagementEstablished Web.canonicalGatesFoundationBoundary ≡ true
gatesRepeatedEngagementAlreadyPaid = refl

mitInstitutionalRelationAlreadyPaid :
  Web.institutionalRelationshipEstablished Web.canonicalMITInstitutionalBoundary ≡ true
mitInstitutionalRelationAlreadyPaid = refl

terramarFundingEdgeAlreadyPaid :
  Web.epsteinFoundationDonation57kEstablished Web.canonicalTerraMarBoundary ≡ true
terramarFundingEdgeAlreadyPaid = refl

freshWebSweepRequiredEveryRound :
  PublicAtlas.freshWebSweepEachRound PublicAtlas.canonicalHubPriorityBoundary ≡ true
freshWebSweepRequiredEveryRound = refl

localPsychedelicFrontierIsNotGlobalFrontier : Bool
localPsychedelicFrontierIsNotGlobalFrontier = true

------------------------------------------------------------------------
-- Promotion / routing firewalls.
------------------------------------------------------------------------

data DenseLaneImpliesGlobalPriority : Set where
data HighProfileNameImpliesWrongdoing : Set where
data InstitutionalContactImpliesIndividualMisconduct : Set where
data FamilyRelationImpliesCorporateControl : Set where
data HistoricalCorporateLineageImpliesEpsteinEraCoordination : Set where
data NetworkPathImpliesCoordination : Set where
data PublicIndexImpliesPaidEdge : Set where

denseLaneDoesNotAutomaticallyCreateGlobalPriority : DenseLaneImpliesGlobalPriority → ⊥
denseLaneDoesNotAutomaticallyCreateGlobalPriority ()

highProfileNameDoesNotImplyWrongdoing : HighProfileNameImpliesWrongdoing → ⊥
highProfileNameDoesNotImplyWrongdoing ()

institutionalContactDoesNotImplyIndividualMisconduct :
  InstitutionalContactImpliesIndividualMisconduct → ⊥
institutionalContactDoesNotImplyIndividualMisconduct ()

familyRelationDoesNotCreateCorporateControl : FamilyRelationImpliesCorporateControl → ⊥
familyRelationDoesNotCreateCorporateControl ()

historicalLineageDoesNotCreateEpsteinEraCoordination :
  HistoricalCorporateLineageImpliesEpsteinEraCoordination → ⊥
historicalLineageDoesNotCreateEpsteinEraCoordination ()

networkPathDoesNotEstablishCoordination : NetworkPathImpliesCoordination → ⊥
networkPathDoesNotEstablishCoordination ()

publicIndexDoesNotPayEdge : PublicIndexImpliesPaidEdge → ⊥
publicIndexDoesNotPayEdge ()
