module DASHI.Cognition.EpsteinGlobalSciencePatronageRouterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Cognition.EpsteinPsychedelicParetoSnowballExact as Psychedelic
import DASHI.Cognition.ChomskyEpsteinRelationshipExact as Chomsky
import DASHI.Cognition.EpsteinSciencePatronageMicrocosmExact as Patronage
import DASHI.Cognition.EpsteinNaturePublishingBoundaryExact as Publishing

------------------------------------------------------------------------
-- GLOBAL EPSTEIN SCIENCE / PATRONAGE ACQUISITION ROUTER
--
-- This owner corrects the over-indexing risk of treating the local
-- psychedelic/consciousness router as if it were the global acquisition front.
-- The local Yu frontier remains valid inside that subproblem. Globally, we
-- retain an exploit/explore portfolio spanning distinct hub types.
--
-- Calibration below routes acquisition effort only. It is not a truth,
-- culpability, wrongdoing, scientific-authority, or relationship-strength
-- score.
------------------------------------------------------------------------

data GlobalLane : Set where
  yuConsciousnessPsychedelics : GlobalLane
  chomskyLanguageBrokerage : GlobalLane
  gatesFoundationPhilanthropy : GlobalLane
  harvardNowakSummersInstitutional : GlobalLane
  mitMediaLabInstitutional : GlobalLane
  maxwellPergamonElsevierPublishing : GlobalLane
  doblinMAPSInstitutionalisation : GlobalLane
  hearstPSFCFundingChronology : GlobalLane
  broadSciencePatronageExploration : GlobalLane

record GlobalLaneStatus : Set where
  constructor global-lane-status
  field
    lane : GlobalLane
    directRelationshipAlreadyEstablished : Bool
    institutionalOrCorporateLineageEstablished : Bool
    primaryCorpusSaturationOpen : Bool
    crossDomainBridgePotential : Bool
    requiresIndependentEdgeReceipt : Bool
    note : String
open GlobalLaneStatus public

yuStatus : GlobalLaneStatus
yuStatus = global-lane-status
  yuConsciousnessPsychedelics true false true true true
  "Dense direct funding/brokerage/altered-state seam; remains local exploitation leader but does not define the global network."

chomskyStatus : GlobalLaneStatus
chomskyStatus = global-lane-status
  chomskyLanguageBrokerage true false true true true
  "Direct repeated relationship already paid in its own owner; acquisition target is functional role, adjacent introductions/projects and independent one-hop expansion."

gatesStatus : GlobalLaneStatus
gatesStatus = global-lane-status
  gatesFoundationPhilanthropy false false true true true
  "2026 external reporting makes Gates/Foundation a high-value global probe; promote only direct meeting/funding/brokerage edges recovered from primary or independently verified records."

harvardStatus : GlobalLaneStatus
harvardStatus = global-lane-status
  harvardNowakSummersInstitutional false true true true true
  "Institutional-science lane: recover donor, programme, researcher and governance edges independently; institutional connection does not imply individual wrongdoing."

mitStatus : GlobalLaneStatus
mitStatus = global-lane-status
  mitMediaLabInstitutional false true true true true
  "Institutional funding/governance lane; keep donation handling, researcher contact and governance response separately typed."

maxwellPublishingStatus : GlobalLaneStatus
maxwellPublishingStatus = global-lane-status
  maxwellPergamonElsevierPublishing false true true true true
  "Historical Maxwell->Pergamon->Elsevier corporate genealogy is separate from any Epstein/Ghislaine-era publishing influence, which remains receipt-dependent."

doblinStatus : GlobalLaneStatus
doblinStatus = global-lane-status
  doblinMAPSInstitutionalisation false true true true true
  "High-upside falsification/probe lane: resolve proposed invite versus actual correspondence, meeting, funding or institutional overlap."

hearstStatus : GlobalLaneStatus
hearstStatus = global-lane-status
  hearstPSFCFundingChronology false true true true true
  "Resolve primary Epstein/Hearst records against PSFC/MAPS chronology without turning temporal proximity into causation."

broadStatus : GlobalLaneStatus
broadStatus = global-lane-status
  broadSciencePatronageExploration false false true true true
  "Exploration reserve for independent hubs in mathematics, AI, genetics/evolution, physics, publishing and institutional science."

------------------------------------------------------------------------
-- Exploit/explore portfolio.
------------------------------------------------------------------------

data AcquisitionMode : Set where
  exploit : AcquisitionMode
  explore : AcquisitionMode
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
  global-acquisition-instruction yuConsciousnessPsychedelics exploit 35 true true
    "Continue Yu whole-thread/attachment/entity saturation, but cap the lane so density cannot monopolise the global router."
  ∷ global-acquisition-instruction chomskyLanguageBrokerage explore 15 true true
    "Expand direct Chomsky relationship one hop through introductions, projects, payments, travel/social and adjacent academics; preserve edge typing."
  ∷ global-acquisition-instruction gatesFoundationPhilanthropy explore 15 true true
    "Acquire Gates/Foundation primary records for meetings, proposed funds, introductions and institutional interaction; external review is locator/context, not a substitute for primary edges."
  ∷ global-acquisition-instruction harvardNowakSummersInstitutional explore 10 true true
    "Recover Harvard/Nowak/Summers donor and governance records, including programme-level funding and independently sourced institutional chronology."
  ∷ global-acquisition-instruction mitMediaLabInstitutional explore 10 true true
    "Recover MIT/Media Lab donation, concealment/governance and researcher-contact edges as separate records."
  ∷ global-acquisition-instruction maxwellPergamonElsevierPublishing falsificationProbe 5 true true
    "Lock the historical publishing genealogy, then search specifically for any contemporaneous Epstein/Ghislaine-era publisher/editor/journal bridge; absent receipt, retain separation."
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
  scienceTopicLayer : NetworkLayer
  governanceLayer : NetworkLayer

data EdgeStatus : Set where
  locatorOnly : EdgeStatus
  sourceObserved : EdgeStatus
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

institutionalContactDoesNotImplyIndividualMisconduct :
  InstitutionalContactImpliesIndividualMisconduct → ⊥
institutionalContactDoesNotImplyIndividualMisconduct ()

familyRelationDoesNotCreateCorporateControl : FamilyRelationImpliesCorporateControl → ⊥
familyRelationDoesNotCreateCorporateControl ()

historicalLineageDoesNotCreateEpsteinEraInfluence :
  HistoricalCorporateLineageImpliesEpsteinEraInfluence → ⊥
historicalLineageDoesNotCreateEpsteinEraInfluence ()

networkPathDoesNotEstablishCoordination : NetworkPathImpliesCoordination → ⊥
networkPathDoesNotEstablishCoordination ()
