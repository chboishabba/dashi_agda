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

------------------------------------------------------------------------
-- GLOBAL EPSTEIN SCIENCE / PATRONAGE ACQUISITION ROUTER
--
-- Corrects local-lane over-indexing. Several lanes are no longer speculative
-- probes: Gates/Foundation, MIT and TerraMar now have concrete institutional or
-- funding receipts. The router therefore allocates acquisition effort to
-- saturating their functional role and one-hop topology, while keeping Yu as a
-- bounded exploitation lane.
--
-- Shares below are search-allocation heuristics, not truth, culpability,
-- wrongdoing, scientific-authority or relationship-strength scores.
------------------------------------------------------------------------

data GlobalLane : Set where
  yuConsciousnessPsychedelics : GlobalLane
  chomskyLanguageBrokerage : GlobalLane
  gatesFoundationPhilanthropy : GlobalLane
  harvardNowakSummersInstitutional : GlobalLane
  mitMediaLabInstitutional : GlobalLane
  maxwellTerraMarNonprofit : GlobalLane
  maxwellPergamonElsevierPublishing : GlobalLane
  doblinMAPSInstitutionalisation : GlobalLane
  hearstPSFCFundingChronology : GlobalLane

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
  "Foundation review establishes 2011-2014 engagement around a proposed public-health DAF and Epstein's IPI introduction; AP reports about 30 meetings. Saturate meeting-by-meeting and adjacent philanthropy topology."

harvardStatus : GlobalLaneStatus
harvardStatus = global-lane-status harvardNowakSummersInstitutional true true true true
  "Nature/Harvard reporting establishes substantial institutional consequence and Epstein science-funding context; recover project, funding, correspondence and governance edges separately."

mitStatus : GlobalLaneStatus
mitStatus = global-lane-status mitMediaLabInstitutional true true true true
  "MIT fact-finding establishes 10 Epstein gifts totaling USD 850k, nine campus visits, and post-conviction donation handling. Expand researcher/donor/broker topology rather than re-proving institutional contact."

terramarStatus : GlobalLaneStatus
terramarStatus = global-lane-status maxwellTerraMarNonprofit true true true true
  "US v Maxwell exhibit establishes a USD 57k Epstein Interests Foundation donation to Ghislaine Maxwell-founded TerraMar. Expand nonprofit, donor, event and institutional edges separately from publishing genealogy."

maxwellPublishingStatus : GlobalLaneStatus
maxwellPublishingStatus = global-lane-status maxwellPergamonElsevierPublishing true true true true
  "Robert Maxwell->Pergamon->Elsevier and Ghislaine family relation are historical facts; contemporaneous Epstein/Ghislaine-era publisher/editor influence still requires a separate receipt."

doblinStatus : GlobalLaneStatus
doblinStatus = global-lane-status doblinMAPSInstitutionalisation false true true true
  "Resolve proposed invite versus actual correspondence, meeting, funding or institutional overlap."

hearstStatus : GlobalLaneStatus
hearstStatus = global-lane-status hearstPSFCFundingChronology false true true true
  "Resolve Epstein/Hearst primary records against PSFC/MAPS chronology without importing causation from timing."

------------------------------------------------------------------------
-- Recalibrated exploit/explore portfolio after web verification.
------------------------------------------------------------------------

data AcquisitionMode : Set where
  exploit : AcquisitionMode
  expandPaidHub : AcquisitionMode
  falsificationProbe : AcquisitionMode

record GlobalAcquisitionInstruction : Set where
  constructor global-acquisition-instruction
  field
    target : GlobalLane
    mode : AcquisitionMode
    relativeShare : Nat
    stopWhenMarginalRedundancyRises : Bool
    requireEdgeLocalProvenance : Bool
    instruction : String
open GlobalAcquisitionInstruction public

currentGlobalAcquisitionPlan : List GlobalAcquisitionInstruction
currentGlobalAcquisitionPlan =
  global-acquisition-instruction yuConsciousnessPsychedelics exploit 25 true true
    "Continue Yu whole-thread/attachment/entity saturation, capped so corpus density cannot monopolise acquisition."
  ∷ global-acquisition-instruction gatesFoundationPhilanthropy expandPaidHub 15 true true
    "Acquire meeting-by-meeting Gates/Foundation records, proposed DAF structure, IPI path and all adjacent brokers/donors introduced through Epstein."
  ∷ global-acquisition-instruction mitMediaLabInstitutional expandPaidHub 15 true true
    "Expand the already-paid MIT relationship through exact donation destinations, researcher contacts, claimed coordinated donations, visits and governance concealment/visibility handling."
  ∷ global-acquisition-instruction chomskyLanguageBrokerage expandPaidHub 10 true true
    "Expand Chomsky one hop through introductions, project administration, payments, travel/social contacts and adjacent academics."
  ∷ global-acquisition-instruction harvardNowakSummersInstitutional expandPaidHub 10 true true
    "Resolve Harvard/Nowak/Summers project funding, correspondence and donor-broker function, not merely institutional fallout."
  ∷ global-acquisition-instruction maxwellTerraMarNonprofit expandPaidHub 10 true true
    "Expand the paid Epstein Foundation->TerraMar edge through donors, events, institutional partners, ocean/science networks and contemporaneous Epstein correspondence."
  ∷ global-acquisition-instruction maxwellPergamonElsevierPublishing falsificationProbe 5 true true
    "Search specifically for contemporaneous publisher/editor/journal bridges while keeping Robert Maxwell corporate genealogy distinct from Ghislaine/Epstein influence."
  ∷ global-acquisition-instruction doblinMAPSInstitutionalisation falsificationProbe 5 true true
    "Resolve every Doblin/MAPS occurrence into invite/contact/meeting/funding/institutional-overlap categories."
  ∷ global-acquisition-instruction hearstPSFCFundingChronology falsificationProbe 5 true true
    "Resolve Hearst/PSFC/MAPS chronology with primary records and no causation promotion."
  ∷ []

------------------------------------------------------------------------
-- Layered graph discipline.
------------------------------------------------------------------------

data NetworkLayer : Set where
  peopleLayer : NetworkLayer
  institutionLayer : NetworkLayer
  moneyLayer : NetworkLayer
  introductionLayer : NetworkLayer
  publishingLayer : NetworkLayer
  nonprofitLayer : NetworkLayer
  scienceTopicLayer : NetworkLayer
  governanceLayer : NetworkLayer

data EdgeStatus : Set where
  locatorOnly : EdgeStatus
  sourceObserved : EdgeStatus
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

localPsychedelicFrontierIsNotGlobalFrontier : Bool
localPsychedelicFrontierIsNotGlobalFrontier = true

------------------------------------------------------------------------
-- Promotion / routing firewalls.
------------------------------------------------------------------------

data DenseLaneImpliesGlobalPriority : Set where
data HighProfileNameImpliesWrongdoing : Set where
data InstitutionalContactImpliesIndividualMisconduct : Set where
data FamilyRelationImpliesCorporateControl : Set where
data HistoricalCorporateLineageImpliesEpsteinEraInfluence : Set where
data NetworkPathImpliesCoordination : Set where

denseLaneDoesNotAutomaticallyCreateGlobalPriority : DenseLaneImpliesGlobalPriority → ⊥
denseLaneDoesNotAutomaticallyCreateGlobalPriority ()

highProfileNameDoesNotImplyWrongdoing : HighProfileNameImpliesWrongdoing → ⊥
highProfileNameDoesNotImplyWrongdoing ()

institutionalContactDoesNotImplyIndividualMisconduct : InstitutionalContactImpliesIndividualMisconduct → ⊥
institutionalContactDoesNotImplyIndividualMisconduct ()

familyRelationDoesNotCreateCorporateControl : FamilyRelationImpliesCorporateControl → ⊥
familyRelationDoesNotCreateCorporateControl ()

historicalLineageDoesNotCreateEpsteinEraInfluence : HistoricalCorporateLineageImpliesEpsteinEraInfluence → ⊥
historicalLineageDoesNotCreateEpsteinEraInfluence ()

networkPathDoesNotEstablishCoordination : NetworkPathImpliesCoordination → ⊥
networkPathDoesNotEstablishCoordination ()
