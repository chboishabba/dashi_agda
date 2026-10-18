module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound8Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- ROUND 8: MATERIAL LIFECYCLE WITH DIRECTLY SITUATED WORKER/COMMUNITY OBSERVERS.
--
-- These sources pay observer/mechanism/context fibres for electronics and
-- digital-material lifecycles. They DO NOT establish that a named Digital-ESD
-- device, platform, school or AI service used material from the observed sites.
------------------------------------------------------------------------

data Round8Residual : Set where
  eWasteWorkingConditionsByWorkerObserver : Round8Residual
  eWasteHazardKnowledgeByLivelihoodChoice : Round8Residual
  eWasteInformalityByWorkerValueChainPosition : Round8Residual
  cobaltExtractionByCommunityPowerGenderChildLabour : Round8Residual

record Round8Candidate : Set where
  constructor round8-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    externalIdentityState : String
    deweyState : String
    targetResidual : Round8Residual
    situatedObserverReading : String
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round8Candidate public

mkRound8Candidate :
  (source : Attr.AttributedSource) →
  String →
  Round8Residual →
  String →
  String →
  String →
  Round8Candidate
mkRound8Candidate source identity residual observer reading limitation =
  round8-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound8Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object article QID recorded by round 8"))
    identity
    "Dewey classification unresolved; no nearest-label substitution"
    residual observer reading limitation false refl

------------------------------------------------------------------------
-- Agbogbloshie: worker conditions/exposures and informal support.
------------------------------------------------------------------------

akormediAsampongFobilSource : Attr.AttributedSource
akormediAsampongFobilSource = Attr.mkDOISource
  "Matthew Akormedi; Emmanuel Asampong; Julius N. Fobil"
  "Working conditions and environmental exposures among electronic waste workers in Ghana"
  "International Journal of Occupational and Environmental Health 19(4), 278-286"
  "2013"
  "10.1179/2049396713Y.0000000034"
  "https://doi.org/10.1179/2049396713Y.0000000034"
  Attr.academicArticleSource
  "Qualitative grounded-theory study using in-depth interviews to describe informal e-waste recycling, working conditions, exposures and worker-created mutual-support arrangements at Agbogbloshie in Accra, Ghana."
  Attr.publicAttribution

akormediCandidate : Round8Candidate
akormediCandidate = mkRound8Candidate
  akormediAsampongFobilSource
  "DOI 10.1179/2049396713Y.0000000034; PMID 24588034 verified"
  eWasteWorkingConditionsByWorkerObserver
  "Informal e-waste workers are direct situated observers of working conditions/exposures and their own support arrangements, rather than being represented only by global waste-flow totals."
  "Pays worker-observer, occupational/externality and informal-support fibres for one Ghanaian e-waste context."
  "Does not establish origin of the e-waste, universal Ghanaian/Global-South worker conditions, or a same-object link to equipment used by a Digital-ESD deployment."

------------------------------------------------------------------------
-- Agbogbloshie: worker knowledge and livelihood alternatives.
------------------------------------------------------------------------

yuAkormediAsampongMeyerFobilSource : Attr.AttributedSource
yuAkormediAsampongMeyerFobilSource = Attr.mkDOISource
  "Emily A. Yu; Matthew Akormedi; Emmanuel Asampong; Christian G. Meyer; Julius N. Fobil"
  "Informal processing of electronic waste at Agbogbloshie, Ghana: workers' knowledge about associated health hazards and alternative livelihoods"
  "Global Health Promotion 24(4), 90-98"
  "2017"
  "10.1177/1757975916631523"
  "https://doi.org/10.1177/1757975916631523"
  Attr.academicArticleSource
  "Qualitative cross-sectional study with twenty all-male e-waste workers at Agbogbloshie investigating workers' knowledge of potential health hazards and their preferred livelihood alternatives."
  Attr.publicAttribution

yuCandidate : Round8Candidate
yuCandidate = mkRound8Candidate
  yuAkormediAsampongMeyerFobilSource
  "DOI 10.1177/1757975916631523; PMID 27271535 verified"
  eWasteHazardKnowledgeByLivelihoodChoice
  "Workers directly report hazard knowledge and preferred alternatives, allowing the hyperfabric to keep exposure, interpretation/knowledge, livelihood dependence and exit preference as distinct coordinates."
  "Pays worker-knowledge x practical livelihood-choice fibres without assuming that awareness alone changes working conditions or that formalisation is automatically preferable."
  "Twenty all-male workers in one site; does not represent women, children, all recyclers, realised ability to exit, or the source chain of a named Digital-ESD device."

------------------------------------------------------------------------
-- Santiago: formal/informal e-waste labour profiles and value-chain positions.
------------------------------------------------------------------------

labraGallegoSchmidMcLachlanSource : Attr.AttributedSource
labraGallegoSchmidMcLachlanSource = Attr.mkDOISource
  "Nicolás Labra Cataldo; Alejandro Gallego-Schmid; Carly McLachlan"
  "Waste pickers in the Global South: understanding the key features that underpin the dominance of informality"
  "Sustainability: Science, Practice and Policy 21(1), 2478697"
  "2025"
  "10.1080/15487733.2025.2478697"
  "https://doi.org/10.1080/15487733.2025.2478697"
  Attr.academicArticleSource
  "Ethnographic study using participant observation and semi-structured interviews with e-waste stakeholders in the Santiago Metropolitan Region, Chile, distinguishing multiple formal/informal labour profiles and value-chain positions."
  Attr.publicAttribution

labraCandidate : Round8Candidate
labraCandidate = mkRound8Candidate
  labraGallegoSchmidMcLachlanSource
  "DOI verified; article-level QID unresolved"
  eWasteInformalityByWorkerValueChainPosition
  "Workers and value-chain actors are observed across different labour positions rather than collapsed into one 'e-waste worker' category, useful for intersectional incidence and political-economy routing."
  "Pays labour-position/formality/value-chain context and direct situated-observer evidence in metropolitan Santiago."
  "Does not establish all Global-South e-waste systems, educational-device provenance, or causal effects of any single formalisation policy."

------------------------------------------------------------------------
-- DRC cobalt: miners/traders/community members, gender/power/child labour.
------------------------------------------------------------------------

sovacoolCobaltSource : Attr.AttributedSource
sovacoolCobaltSource = Attr.mkDOISource
  "Benjamin K. Sovacool"
  "When subterranean slavery supports sustainability transitions? power, patriarchy, and child labor in artisanal Congolese cobalt mining"
  "The Extractive Industries and Society 8(1), 271-293"
  "2021"
  "10.1016/j.exis.2020.11.018"
  "https://doi.org/10.1016/j.exis.2020.11.018"
  Attr.academicArticleSource
  "Original DRC field research including 23 expert interviews, 48 community interviews with artisanal miners/traders/community members, and visits to 17 mines, processing centres and trading depots; analyses power, dispossession, gender relations and child labour in cobalt extraction."
  Attr.publicAttribution

sovacoolCandidate : Round8Candidate
sovacoolCandidate = mkRound8Candidate
  sovacoolCobaltSource
  "DOI verified; article-level QID unresolved"
  cobaltExtractionByCommunityPowerGenderChildLabour
  "Miners, traders and community members enter the evidence fabric as situated observers of extraction and power rather than appearing only as a material-source label. Gendered and child-labour dimensions remain separately visible."
  "High-alpha source for material lifecycle x political economy x gender/community/worker incidence in a digital-device material context."
  "Cobalt has many end uses and supply chains. This source does not establish that cobalt in any named educational device/service came from these artisanal sites, nor that all DRC cobalt production shares these conditions."

canonicalRound8Frontier : List Round8Candidate
canonicalRound8Frontier =
  akormediCandidate
  ∷ yuCandidate
  ∷ labraCandidate
  ∷ sovacoolCandidate
  ∷ []

------------------------------------------------------------------------
-- Same-object / authority firewalls.
------------------------------------------------------------------------

data Round8CandidateCreatesIncludedStudy : Set where
data WorkerStudyCreatesDigitalESDDeploymentSupplyChainIdentity : Set where
data LocalWorkerObservationCreatesUniversalLifecycleWorkerState : Set where
data CobaltContextCreatesNamedDeviceMaterialOrigin : Set where
data WorkerHazardKnowledgeCreatesRealisedExitCapacity : Set where
data EWasteContextCreatesWholeLifecycleMeasurement : Set where

round8CandidateDoesNotCreateIncludedStudy : Round8CandidateCreatesIncludedStudy → ⊥
round8CandidateDoesNotCreateIncludedStudy ()

workerStudyDoesNotCreateDigitalESDDeploymentSupplyChainIdentity :
  WorkerStudyCreatesDigitalESDDeploymentSupplyChainIdentity → ⊥
workerStudyDoesNotCreateDigitalESDDeploymentSupplyChainIdentity ()

localWorkerObservationDoesNotCreateUniversalLifecycleWorkerState :
  LocalWorkerObservationCreatesUniversalLifecycleWorkerState → ⊥
localWorkerObservationDoesNotCreateUniversalLifecycleWorkerState ()

cobaltContextDoesNotCreateNamedDeviceMaterialOrigin :
  CobaltContextCreatesNamedDeviceMaterialOrigin → ⊥
cobaltContextDoesNotCreateNamedDeviceMaterialOrigin ()

workerHazardKnowledgeDoesNotCreateRealisedExitCapacity :
  WorkerHazardKnowledgeCreatesRealisedExitCapacity → ⊥
workerHazardKnowledgeDoesNotCreateRealisedExitCapacity ()

eWasteContextDoesNotCreateWholeLifecycleMeasurement :
  EWasteContextCreatesWholeLifecycleMeasurement → ⊥
eWasteContextDoesNotCreateWholeLifecycleMeasurement ()
