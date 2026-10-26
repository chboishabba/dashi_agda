module DASHI.Cognition.PsychologicalInfluenceInfrastructureCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.CognitiveWarfareAdmissibleDetectionExact as Detection
import DASHI.Governance.InstitutionalTechniqueTransferCore as Transfer
import DASHI.Cognition.BannonCambridgeAnalyticaInfluenceInfrastructureExact as CA
import DASHI.Cognition.BannonCambridgeAnalyticaSystemicLeverageBridgeExact as CASystem
import DASHI.Cognition.TrumpMarALagoBannonBridgeExact as Bannon
import DASHI.Cognition.TurningPointEpsteinNarrativePressureExact as TPUSA
import DASHI.Cognition.HeritageProject2025TrumpImplementationExact as P2025
import DASHI.Cognition.MavenPalantirIsraelPineGapSecurityInfrastructureExact as Security
import DASHI.Cognition.StateInstitutionEpistemicNonPrivilegeExact as NonPrivilege

------------------------------------------------------------------------
-- PSYCHOLOGICAL / COGNITIVE INFLUENCE INFRASTRUCTURE CROSS-POLLINATION
--
-- Reuses the observer-relative cognitive-warfare theorem and the generic
-- institutional-technique-transfer distinction. The live actors below are not
-- collapsed into one programme merely because each has documented interests in
-- persuasion, targeting, narrative control, audience selection, policy
-- implementation, surveillance or decision support.
------------------------------------------------------------------------

data InfluenceStage : Set where
  acquireAudienceData : InfluenceStage
  inferAudienceState : InfluenceStage
  segmentAudience : InfluenceStage
  frameMessage : InfluenceStage
  distributeMessage : InfluenceStage
  reinforceFeedback : InfluenceStage
  measureResponse : InfluenceStage
  gateInformation : InfluenceStage
  institutionalisePolicy : InfluenceStage
  operationaliseDecision : InfluenceStage

data LiveSurface : Set where
  bannonCambridgeAnalytica : LiveSurface
  bannonEpsteinMedia : LiveSurface
  trumpMarALagoPoliticalMedia : LiveSurface
  turningPointNarrativePressure : LiveSurface
  heritageProject2025 : LiveSurface
  palantirMavenStateData : LiveSurface
  proIsraelAdvocacy : LiveSurface
  oracleEllisonSiblingPR : LiveSurface

record InfluenceProfile : Set where
  constructor influence-profile
  field
    surface : LiveSurface
    documentedInterest : Bool
    documentedCapability : Bool
    documentedDeployment : Bool
    measuredEffect : Bool
    outcomeCausationPaid : Bool
    techniqueTransferPaid : Bool
    stages : List InfluenceStage
    reading : String
open InfluenceProfile public

canonicalProfiles : List InfluenceProfile
canonicalProfiles =
  influence-profile bannonCambridgeAnalytica true true true true false false
    (acquireAudienceData ∷ inferAudienceState ∷ segmentAudience ∷ frameMessage ∷ distributeMessage ∷ measureResponse ∷ [])
    "Bannon/CA pays an influence stack spanning data, segmentation, targeting, framing and campaign delivery. Apparatus existence and deployment do not pay election-outcome causation."
  ∷ influence-profile bannonEpsteinMedia true true true false false false
    (frameMessage ∷ distributeMessage ∷ gateInformation ∷ [])
    "Bannon/Epstein pays sustained media-rehabilitation and political-messaging work. Similarity to Bannon's earlier influence practice does not by itself pay same-technique transfer."
  ∷ influence-profile trumpMarALagoPoliticalMedia true true true false false false
    (frameMessage ∷ distributeMessage ∷ gateInformation ∷ reinforceFeedback ∷ [])
    "Trump-world/Mar-a-Lago/Bannon supplies access, agenda and narrative infrastructure. It is not thereby one centrally commanded psychological operation."
  ∷ influence-profile turningPointNarrativePressure true true true false false false
    (frameMessage ∷ distributeMessage ∷ reinforceFeedback ∷ gateInformation ∷ [])
    "TPUSA supplies a high-capacity audience/distribution surface and a documented Epstein-files pressure/attenuation episode. Leadership response does not prove covert state direction."
  ∷ influence-profile heritageProject2025 true true true true false false
    (frameMessage ∷ institutionalisePolicy ∷ operationaliseDecision ∷ [])
    "Project 2025 converts an articulated political programme into personnel, training, policy and implementation capacity. This is political/state-capacity infrastructure, not automatically psychological warfare."
  ∷ influence-profile palantirMavenStateData true true true true false false
    (acquireAudienceData ∷ inferAudienceState ∷ gateInformation ∷ operationaliseDecision ∷ [])
    "Palantir/Maven/state-data systems create observer-to-decision infrastructure. Kinetic/intelligence targeting is structurally comparable at the observer/selection layer but is not semantically identical to psychological warfare."
  ∷ influence-profile proIsraelAdvocacy true true true true false false
    (frameMessage ∷ distributeMessage ∷ reinforceFeedback ∷ institutionalisePolicy ∷ [])
    "Public lobbying/election-spending infrastructure pays political influence capacity. It does not establish secret command, universal message discipline or procurement control."
  ∷ influence-profile oracleEllisonSiblingPR true true true false false false
    (acquireAudienceData ∷ inferAudienceState ∷ operationaliseDecision ∷ [])
    "Sibling PR #1112 source-writes an Oracle/Ellison surveillance-security cognitive-warfare weld. Because that PR is unmerged, this branch records the adjacency without importing it as theorem authority."
  ∷ []

record InfluenceInfrastructureBoundary : Set where
  constructor influence-infrastructure-boundary
  field
    sharedInfluenceInterestImpliesCoordination : Bool
    sharedVendorImpliesCommonCommand : Bool
    capabilityImpliesDeployment : Bool
    deploymentImpliesMeasuredEffect : Bool
    measuredEffectImpliesOutcomeCausation : Bool
    techniqueSimilarityImpliesTechniqueTransfer : Bool
    targetVisibleMessageDeterminesProvenance : Bool
    militaryDecisionSupportIsPsychologicalWarfare : Bool
    politicalAdvocacyIsCovertPsychologicalWarfare : Bool
    influenceIntersectionWorthAcquiring : Bool
open InfluenceInfrastructureBoundary public

canonicalInfluenceInfrastructureBoundary : InfluenceInfrastructureBoundary
canonicalInfluenceInfrastructureBoundary = influence-infrastructure-boundary
  false false false false false false false false false true

data SharedInterestImpliesCoordination : Set where
data SimilarTechniqueImpliesTransfer : Set where
data DeploymentImpliesOutcomeCause : Set where
data KineticTargetingImpliesPsychologicalWarfare : Set where

sharedInterestDoesNotCreateCoordination : SharedInterestImpliesCoordination → ⊥
sharedInterestDoesNotCreateCoordination ()

similarTechniqueDoesNotCreateTransfer : SimilarTechniqueImpliesTransfer → ⊥
similarTechniqueDoesNotCreateTransfer ()

deploymentDoesNotCreateOutcomeCause : DeploymentImpliesOutcomeCause → ⊥
deploymentDoesNotCreateOutcomeCause ()

kineticTargetingDoesNotCreatePsychologicalWarfare : KineticTargetingImpliesPsychologicalWarfare → ⊥
kineticTargetingDoesNotCreatePsychologicalWarfare ()

------------------------------------------------------------------------
-- Acquisition targets: same-object receipts, not similarity.
------------------------------------------------------------------------

data TechniqueTransferDebt : Set where
  caToEpsteinMediaSameTechnique : TechniqueTransferDebt
  campaignTargetingToTPUSASameTechnique : TechniqueTransferDebt
  politicalInfluenceToStatePersonnelSameTechnique : TechniqueTransferDebt
  advocacyToProcurementSelectionSameTechnique : TechniqueTransferDebt
  surveillanceToPersuasionSameTechnique : TechniqueTransferDebt

record TransferAcquisition : Set where
  constructor transfer-acquisition
  field
    debt : TechniqueTransferDebt
    routingPriority : Nat
    requiresPersonnelOrMethodReceipt : Bool
    requiresSameObjectEvidence : Bool
    question : String
open TransferAcquisition public

canonicalTransferAcquisition : List TransferAcquisition
canonicalTransferAcquisition =
  transfer-acquisition caToEpsteinMediaSameTechnique 100 true true
    "Do Bannon's Epstein rehabilitation materials reuse a documented Cambridge-Analytica/SCL method, personnel, workflow, measurement loop or targeting artifact on the same object?"
  ∷ transfer-acquisition politicalInfluenceToStatePersonnelSameTechnique 96 true true
    "Which influence/selection techniques pass from campaign/think-tank environments into Project-2025 personnel, training or administrative implementation with explicit receipts?"
  ∷ transfer-acquisition campaignTargetingToTPUSASameTechnique 94 true true
    "Do TPUSA audience/distribution systems reuse identifiable campaign-targeting methods beyond ordinary political communications?"
  ∷ transfer-acquisition advocacyToProcurementSelectionSameTechnique 90 true true
    "Can any advocacy/lobbying edge be tied to a specific vendor or procurement decision rather than inferred from ideological alignment?"
  ∷ transfer-acquisition surveillanceToPersuasionSameTechnique 88 true true
    "Where do surveillance/legibility systems actually feed persuasion or narrative-selection loops, rather than merely sharing data/observer topology?"
  ∷ []
