module DASHI.Biology.IBSTransitionTriggerAtlasExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.IBSLatentStateTransitionExact as Latent
import DASHI.Biology.IBSGutBrainImmuneSystemsHyperfabricExact as Whole
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball

lupu2023Source : Source.AttributedSource
lupu2023Source = Source.mkDOISource
  "Vasile Valeriu Lupu; Cristina Mihaela Ghiciuc; Gabriela Stefanescu; Cristina Maria Mihai; Alina Popp; Maria Oana Sasaran; Laura Bozomitu; Iuliana Magdalena Starcea; Anca Adam Raileanu; Ancuta Lupu"
  "Emerging role of the gut microbiome in post-infectious irritable bowel syndrome: A literature review"
  "World Journal of Gastroenterology 29(21):3241-3256" "2023"
  "10.3748/wjg.v29.i21.3241"
  "https://doi.org/10.3748/wjg.v29.i21.3241"
  Source.academicArticleSource
  "Review-level support for post-infectious IBS as persistent symptoms after an acute enteric infection, with candidate microbiome, barrier, immune, neuromuscular and visceral-sensitivity mechanisms. Infection is a natural perturbation, not a unique-mechanism identifier or attractor validation."
  Source.publicAttribution

fowler2025Source : Source.AttributedSource
fowler2025Source = Source.mkDOISource
  "Sophie Fowler; Laura R C Dowling; Nicole Simm; Nicholas J Talley; Grace L Burns; Simon Keely"
  "Sleep Disturbances, Fatigue and Immune Markers in the Irritable Bowel Syndrome and Inflammatory Bowel Disease, a Systematic Review"
  "Neurogastroenterology and Motility 37(11):e70133" "2025"
  "10.1111/nmo.70133"
  "https://doi.org/10.1111/nmo.70133"
  Source.academicArticleSource
  "Review-level support for sleep/fatigue disturbance and GI disease severity associations, with circadian and immune pathways discussed as plausible interacting mechanisms. It does not establish sleep disturbance as the unique driver of IBS transitions."
  Source.publicAttribution

veldman2026Source : Source.AttributedSource
veldman2026Source = Source.mkDOISource
  "Fleur Veldman; Michelle Bosman; Ali Rezaie; Sarvee Moosavi; Daniel Keszthelyi"
  "Wearable-Based Monitoring of Autonomic and Gastrointestinal Function in Disorders of Gut-Brain Interaction: A Systematic Review and Meta-Analyses"
  "Neurogastroenterology and Motility 38(1):e70232" "2026"
  "10.1111/nmo.70232"
  "https://doi.org/10.1111/nmo.70232"
  Source.academicArticleSource
  "Systematic-review/meta-analytic support for wearable HRV, sleep and gastric-myoelectric monitoring as candidate DGBI measurement surfaces; heterogeneity and incomplete clinical validation are retained. Wearable proxies do not identify the latent whole-system state."
  Source.publicAttribution

data TriggerKind : Set where
  acuteEntericInfection : TriggerKind
  dietChallenge : TriggerKind
  microbiomeDirectedIntervention : TriggerKind
  bileAcidPerturbation : TriggerKind
  psychosocialContextPerturbation : TriggerKind
  sleepCircadianPerturbation : TriggerKind
  candidateLocalImmunePerturbation : TriggerKind

data TriggerEvidenceClass : Set where
  naturalExperiment : TriggerEvidenceClass
  randomizedProbe : TriggerEvidenceClass
  intensiveObservational : TriggerEvidenceClass
  reviewBoundedCandidate : TriggerEvidenceClass
  proposedExperiment : TriggerEvidenceClass

record TransitionTrigger : Set where
  constructor transition-trigger
  field
    kind : TriggerKind
    evidenceClass : TriggerEvidenceClass
    sourceReference : String
    proximalFibres : String
    downstreamFibres : String
    persistenceReference : String
    uniqueMechanismIdentified : Bool
    latentStateTransitionProved : Bool
open TransitionTrigger public

postInfectiousTrigger : TransitionTrigger
postInfectiousTrigger = transition-trigger
  acuteEntericInfection naturalExperiment
  "Lupu et al. 2023 DOI 10.3748/wjg.v29.i21.3241 plus established PI-IBS cohort literature"
  "microbiome, epithelial barrier, mucosal immune and neuromuscular perturbation"
  "visceral sensitivity, motility/secretion and gut-brain symptom state"
  "persistent post-infectious symptoms after resolution of acute infection are documented; persistence alone does not identify one maintaining mechanism"
  false false

sleepCircadianTrigger : TransitionTrigger
sleepCircadianTrigger = transition-trigger
  sleepCircadianPerturbation reviewBoundedCandidate
  "Fowler et al. 2025 DOI 10.1111/nmo.70133"
  "sleep/circadian context with autonomic, endocrine and immune coupling"
  "GI symptoms, fatigue, quality of life and potentially visceral-sensitivity state"
  "association and bidirectionality are discussed; intervention-defined transition thresholds are not paid"
  false false

wearableObservationTrigger : TransitionTrigger
wearableObservationTrigger = transition-trigger
  psychosocialContextPerturbation intensiveObservational
  "Veldman et al. 2026 DOI 10.1111/nmo.70232"
  "wearable HRV/sleep/GI myoelectric proxies"
  "candidate synchronized autonomic/GI trajectories"
  "measurement feasibility/heterogeneity evidence only; wearable readout is not itself a perturbation or latent-state identifier"
  false false

canonicalIBSTransitionTriggerAtlas : List TransitionTrigger
canonicalIBSTransitionTriggerAtlas =
  postInfectiousTrigger ∷ sleepCircadianTrigger ∷ wearableObservationTrigger ∷ []

data NaturalTriggerIdentifiesUniqueMechanismPermission : Set where
naturalTriggerDoesNotIdentifyUniqueMechanism : NaturalTriggerIdentifiesUniqueMechanismPermission → ⊥
naturalTriggerDoesNotIdentifyUniqueMechanism ()

data WearableProxyIdentifiesLatentStatePermission : Set where
wearableProxyDoesNotIdentifyLatentState : WearableProxyIdentifiesLatentStatePermission → ⊥
wearableProxyDoesNotIdentifyLatentState ()

data PostInfectiousPersistenceValidatesAttractorPermission : Set where
postInfectiousPersistenceDoesNotValidateAttractor : PostInfectiousPersistenceValidatesAttractorPermission → ⊥
postInfectiousPersistenceDoesNotValidateAttractor ()

record TransitionTriggerParetoNode : Set where
  constructor transition-trigger-pareto-node
  field
    label : String
    route : Snowball.DiscoveryRoute
    paidReference : String
    systemValue : String
    nextAcquisition : String
    attributionBoundary : String
open TransitionTriggerParetoNode public

postInfectiousNaturalProbeNode : TransitionTriggerParetoNode
postInfectiousNaturalProbeNode = transition-trigger-pareto-node
  "post-infectious onset as natural whole-system perturbation"
  Snowball.externalKnowledgeComparison
  "PI-IBS literature: acute infection can precede persistent IBS phenotype in a subset"
  "high-value temporal anchor because trigger time is comparatively well localized and several fibres are plausibly perturbed together"
  "prospective pre/post infection or outbreak cohorts with repeated barrier, immune, microbial-function, autonomic, visceral-sensitivity and symptom measurements"
  "natural perturbation does not isolate which fibre is necessary or sufficient"

wearableDenseSamplingNode : TransitionTriggerParetoNode
wearableDenseSamplingNode = transition-trigger-pareto-node
  "wearable-assisted dense temporal sampling"
  Snowball.experimentalDesign
  "Veldman 2026 review/meta-analysis supports candidate HRV/sleep/GI wearable surfaces with substantial heterogeneity"
  "raises temporal resolution between sparse lab visits and EMA, enabling alignment of autonomic/sleep context with symptom and stool/metabolome events"
  "prospective standardized wearable+EMA+stool/event-triggered protocol with device calibration and missingness ledger"
  "wearable signals are proxies; validation and synchronization errors must remain explicit"

sleepCircadianNode : TransitionTriggerParetoNode
sleepCircadianNode = transition-trigger-pareto-node
  "sleep/circadian modulation of IBS state"
  Snowball.externalKnowledgeComparison
  "Fowler 2025 review supports association among sleep disturbance, fatigue and GI disease severity with immune/circadian context"
  "adds a time-of-day/recovery coordinate that may condition autonomic, immune and sensory gain"
  "intervention or natural schedule-shift studies with objective sleep/circadian measurement and next-day multi-fibre outcomes"
  "association is not a causal sleep→IBS transition law"

historyAwareProbeNode : TransitionTriggerParetoNode
historyAwareProbeNode = transition-trigger-pareto-node
  "history-aware repeated perturbation"
  Snowball.experimentalDesign
  "Latent.canonicalIBSTemporalPathBoundary requires path/history retention structurally"
  "tests whether response depends on how the same apparent present state was reached"
  "counterbalanced repeated challenge with entry/recovery/washout periods and matched present-state measurements"
  "only reproducible path-dependent response would support hysteresis; the design itself does not"

canonicalTransitionTriggerParetoFrontier : List TransitionTriggerParetoNode
canonicalTransitionTriggerParetoFrontier =
  postInfectiousNaturalProbeNode ∷ wearableDenseSamplingNode ∷ sleepCircadianNode ∷ historyAwareProbeNode ∷ []

record IBSTransitionTriggerBoundary : Set where
  constructor ibs-transition-trigger-boundary
  field
    naturalPerturbationsRetained : Bool
    sleepCircadianContextRetained : Bool
    wearablesMayIncreaseTemporalResolution : Bool
    naturalTriggerEqualsUniqueMechanism : Bool
    wearableProxyEqualsLatentState : Bool
    persistentPostInfectiousPhenotypeEqualsAttractorProof : Bool
    historyAwarePerturbationPreferredForHysteresisTest : Bool

canonicalIBSTransitionTriggerBoundary : IBSTransitionTriggerBoundary
canonicalIBSTransitionTriggerBoundary = ibs-transition-trigger-boundary
  true true true false false false true
