module DASHI.Biology.IBSLatentStateTransitionExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.IBSSystemsIdentificationParetoExact as Systems
import DASHI.Biology.IBSGutBrainImmuneSystemsHyperfabricExact as Whole
import DASHI.Core.TemporalValidityPathDependenceExact as Temporal
import DASHI.Cognition.PNF.AttractorMeasurementValidation as AttractorValidation
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball

------------------------------------------------------------------------
-- IBS LATENT-STATE / TRANSITION RECONSTRUCTION
--
-- Attribution rule: empirical sources below pay only their reported temporal
-- observations/designs.  Terms such as regime, latent state, attractor and
-- hysteresis are repository-side structural hypotheses until a named
-- validation receipt discharges the relevant empirical obligations.
------------------------------------------------------------------------

mars2020Source : Source.AttributedSource
mars2020Source = Source.mkDOISource
  "Ruben A T Mars et al."
  "Longitudinal Multi-omics Reveals Subset-Specific Mechanisms Underlying Irritable Bowel Syndrome"
  "Cell 182(6):1460-1473.e17" "2020"
  "10.1016/j.cell.2020.08.007"
  "https://doi.org/10.1016/j.cell.2020.08.007"
  Source.academicArticleSource
  "Pays longitudinal multi-omics observations including flare sampling, subtype- and symptom-related microbial/metabolic variation, and person-specific flare-associated features. It does not establish a universal microbial precursor, causal direction, attractor, or hysteresis law."
  Source.publicAttribution

chan2019Source : Source.AttributedSource
chan2019Source = Source.mkDOISource
  "Y K Chan et al."
  "The temporal relationship of daily life stress, emotions, and bowel symptoms in irritable bowel syndrome-Diarrhea subtype: A smartphone-based experience sampling study"
  "Neurogastroenterology and Motility 31(3):e13514" "2019"
  "10.1111/nmo.13514"
  "https://doi.org/10.1111/nmo.13514"
  Source.academicArticleSource
  "Pays intensive smartphone experience-sampling evidence in IBS-D with time-lagged associations between stress, bowel symptoms and affect. The reported direction is cohort/design-specific and is not promoted to a universal stress-to-IBS law."
  Source.publicAttribution

yunusova2026Source : Source.AttributedSource
yunusova2026Source = Source.mkDOISource
  "Asal Yunusova; David J Levinthal; Phoebe Lam; Kirk Warren Brown; Zach Branson; Sarah Wu; Bethany Sanov; Ava Liccione; Janine M Dutcher; Emily K Lindsay; J David Creswell"
  "Beyond Chronic Stress: Daily Stress Is Associated With Symptoms in Irritable Bowel Syndrome"
  "Clinical Gastroenterology and Hepatology" "2026"
  "10.1016/j.cgh.2026.05.008"
  "https://doi.org/10.1016/j.cgh.2026.05.008"
  Source.academicArticleSource
  "Pays a 357-participant prospective observational EMA surface: momentary stress and IBS symptom severity covary within people, while fully adjusted prospective lagged effects were not established as a robust bidirectional universal law."
  Source.publicAttribution

chen2026Source : Source.AttributedSource
chen2026Source = Source.mkDOISource
  "Jie Chen; Aolan Li; Weizi Wu; Wanli Xu; Tingting Zhao; Angela R Starkweather; Leonel Rodriguez; Ming-Hui Chen; Xiaomei S Cong"
  "Gut microbiota signatures differentiate trajectory-defined response phenotypes and predict self-management outcomes in irritable bowel syndrome"
  "Frontiers in Microbiomes 5:1884540" "2026"
  "10.3389/frmbi.2026.1884540"
  "https://doi.org/10.3389/frmbi.2026.1884540"
  Source.academicArticleSource
  "Pays trajectory-defined response phenotypes over 12 weeks and associations/prediction from baseline microbial composition/function in an ancillary randomized-trial dataset. A statistical trajectory cluster is not thereby a dynamical attractor or mechanistic subtype."
  Source.publicAttribution

data TemporalEvidenceKind : Set where
  longitudinalMultiOmics : TemporalEvidenceKind
  intensiveEMA : TemporalEvidenceKind
  trajectoryClustering : TemporalEvidenceKind
  flareTriggeredSampling : TemporalEvidenceKind

data TemporalDirectionStatus : Set where
  contemporaneousAssociation : TemporalDirectionStatus
  laggedAssociationObserved : TemporalDirectionStatus
  heterogeneousLagDirection : TemporalDirectionStatus
  directionUnresolved : TemporalDirectionStatus

record TemporalStateEvidence : Set where
  constructor temporal-state-evidence
  field
    source : Source.AttributedSource
    kind : TemporalEvidenceKind
    populationReference : String
    samplingReference : String
    observedTemporalSurface : String
    directionStatus : TemporalDirectionStatus
    individualHeterogeneityRetained : Bool
    causalDirectionEstablished : Bool
    attractorValidated : Bool
    hysteresisValidated : Bool
open TemporalStateEvidence public

marsFlareEvidence : TemporalStateEvidence
marsFlareEvidence = temporal-state-evidence
  mars2020Source flareTriggeredSampling
  "IBS-C / IBS-D longitudinal cohort; subset supplied self-identified flare samples"
  "repeated stool/multi-omics plus symptom severity; flare-triggered extra sampling"
  "flare samples and individual time courses showed microbial/metabolic changes, with person-specific features"
  heterogeneousLagDirection true false false false

chanEMAEvidence : TemporalStateEvidence
chanEMAEvidence = temporal-state-evidence
  chan2019Source intensiveEMA
  "27 IBS-D and 30 healthy controls"
  "8 smartphone assessments/day for 14 days"
  "bowel symptoms, stress and affect showed time-dependent relationships; reported lag direction was not the naive stress-worsens-next-symptom rule"
  laggedAssociationObserved true false false false

yunusovaEMAEvidence : TemporalStateEvidence
unusovaEMAEvidence = temporal-state-evidence
  yunusova2026Source intensiveEMA
  "357 adults meeting Rome IV IBS criteria"
  "3 EMA surveys/day for 7 days"
  "within-person momentary stress and symptoms covaried; fully adjusted prospective lagged effects did not establish a universal direction"
  directionUnresolved true false false false

chenTrajectoryEvidence : TemporalStateEvidence
chenTrajectoryEvidence = temporal-state-evidence
  chen2026Source trajectoryClustering
  "62 participants with longitudinal self-management trial data"
  "12-week multidimensional symptom/QOL/psychoneurological trajectories with baseline microbiota features"
  "trajectory-defined response phenotypes and microbial signatures/predictive features"
  directionUnresolved true false false false

canonicalTemporalStateEvidenceAtlas : List TemporalStateEvidence
canonicalTemporalStateEvidenceAtlas =
  marsFlareEvidence ∷ chanEMAEvidence ∷ yunusovaEMAEvidence ∷ chenTrajectoryEvidence ∷ []

------------------------------------------------------------------------
-- Structural latent-state model.  These constructors organise hypotheses;
-- empirical source rows above do not assert that these states literally exist.
------------------------------------------------------------------------

data IBSLatentRegimeCandidate : Set where
  relativelyStableCandidate : IBSLatentRegimeCandidate
  flareCandidate : IBSLatentRegimeCandidate
  recoveryCandidate : IBSLatentRegimeCandidate
  interventionResponseCandidate : IBSLatentRegimeCandidate

data TransitionEvidenceGrade : Set where
  observedTrajectoryDifference : TransitionEvidenceGrade
  temporallyOrderedAssociation : TransitionEvidenceGrade
  controlledPerturbationTransition : TransitionEvidenceGrade
  replicatedStateTransition : TransitionEvidenceGrade

record CandidateStateTransition : Set where
  constructor candidate-state-transition
  field
    fromCandidate : IBSLatentRegimeCandidate
    toCandidate : IBSLatentRegimeCandidate
    grade : TransitionEvidenceGrade
    measuredAxesReference : String
    timeResolutionReference : String
    perturbationReference : String
    historyReference : String
    empiricalStatusReference : String
open CandidateStateTransition public

flareTransitionCandidate : CandidateStateTransition
flareTransitionCandidate = candidate-state-transition
  relativelyStableCandidate flareCandidate observedTrajectoryDifference
  "symptoms + microbiome/metabolites; Mars 2020 flare subset"
  "study-visit longitudinal sampling plus participant-triggered flare sample"
  "no randomized perturbation establishes flare entry direction"
  "prior state/history retained; flare sample is not treated as memoryless"
  "candidate transition suggested by temporal observations; no attractor/hysteresis validation"

------------------------------------------------------------------------
-- Non-identifiability / attribution firewalls.
------------------------------------------------------------------------

data SameSymptomsIdentifySameLatentStatePermission : Set where
sameSymptomsDoNotIdentifySameLatentState : SameSymptomsIdentifySameLatentStatePermission → ⊥
sameSymptomsDoNotIdentifySameLatentState ()

data LagAssociationIdentifiesCausalDirectionPermission : Set where
lagAssociationDoesNotIdentifyCausalDirection : LagAssociationIdentifiesCausalDirectionPermission → ⊥
lagAssociationDoesNotIdentifyCausalDirection ()

data TrajectoryClusterIsValidatedAttractorPermission : Set where
trajectoryClusterDoesNotValidateAttractor : TrajectoryClusterIsValidatedAttractorPermission → ⊥
trajectoryClusterDoesNotValidateAttractor ()

data FlareRemissionDifferenceProvesHysteresisPermission : Set where
flareRemissionDifferenceDoesNotProveHysteresis : FlareRemissionDifferenceProvesHysteresisPermission → ⊥
flareRemissionDifferenceDoesNotProveHysteresis ()

------------------------------------------------------------------------
-- Existing temporal/path and attractor-validation owners.
------------------------------------------------------------------------

record IBSTemporalPathBoundary : Set where
  constructor ibs-temporal-path-boundary
  field
    temporalPathOwner : Temporal.TemporalPathBoundary
    attractorAuthorityOwner : AttractorValidation.AttractorAuthorityBoundary
    currentSymptomsNeedNotEncodeHistory : Bool
    equalCurrentSymptomsNeedNotImplyEqualNextResponse : Bool
    flareRemissionLabelsAreNotValidatedAttractors : Bool
    hysteresisRequiresPathDependentResponseEvidence : Bool
    lagStructureMayBePersonAndTimescaleSpecific : Bool
open IBSTemporalPathBoundary public

canonicalIBSTemporalPathBoundary : IBSTemporalPathBoundary
canonicalIBSTemporalPathBoundary = ibs-temporal-path-boundary
  Temporal.canonicalTemporalPathBoundary
  AttractorValidation.canonicalAttractorAuthorityBoundary
  true true true true true

------------------------------------------------------------------------
-- Pareto acquisition frontier: prioritise temporal interventions that separate
-- regime candidates and direction rather than collecting more cross-sections.
------------------------------------------------------------------------

data TransitionAcquisitionStatus : Set where
  paidLongitudinalObservation : TransitionAcquisitionStatus
  paidTrajectoryStratification : TransitionAcquisitionStatus
  denseMultifibreNeeded : TransitionAcquisitionStatus
  perturbationalTransitionNeeded : TransitionAcquisitionStatus
  hysteresisTestNeeded : TransitionAcquisitionStatus
  replicationNeeded : TransitionAcquisitionStatus

record TransitionParetoNode : Set where
  constructor transition-pareto-node
  field
    label : String
    status : TransitionAcquisitionStatus
    route : Snowball.DiscoveryRoute
    paidReference : String
    missingDiscriminator : String
    nextAcquisition : String
    attributionBoundary : String
open TransitionParetoNode public

flareDynamicsNode : TransitionParetoNode
flareDynamicsNode = transition-pareto-node
  "within-person flare-entry and recovery dynamics"
  paidLongitudinalObservation Snowball.externalKnowledgeComparison
  "Mars 2020 longitudinal multi-omics + flare-triggered sampling"
  "dense pre-flare and post-flare sampling across immune/barrier/autonomic/sensory fibres"
  "event-triggered dense sampling plus recovery follow-up"
  "observed flare association is not a causal entry law"

stressSymptomLagNode : TransitionParetoNode
stressSymptomLagNode = transition-pareto-node
  "stress-symptom lag topology"
  paidLongitudinalObservation Snowball.externalKnowledgeComparison
  "Chan 2019 and Yunusova 2026 EMA provide nonidentical lag results"
  "person-specific and timescale-specific direction under measured autonomic/context state"
  "high-frequency EMA plus autonomic/body-state streams and perturbational stress/context designs where ethical"
  "conflicting/heterogeneous lag findings block a universal scalar stress→symptom transition"

trajectoryPhenotypeNode : TransitionParetoNode
trajectoryPhenotypeNode = transition-pareto-node
  "trajectory-defined response phenotype"
  paidTrajectoryStratification Snowball.externalKnowledgeComparison
  "Chen et al. 2026 longitudinal trajectory clustering with microbial predictors"
  "external replication and intervention-sensitive stability of cluster membership"
  "held-out multi-site trajectory reconstruction with common measurement contract"
  "cluster label is statistical stratification, not attractor validation"

hysteresisNode : TransitionParetoNode
hysteresisNode = transition-pareto-node
  "IBS path-dependence / hysteresis test"
  hysteresisTestNeeded Snowball.experimentalDesign
  "repository TemporalValidityPathDependenceExact provides the structural obligation only"
  "show equal present measured state with different prior paths yields reproducibly different future response, or separated entry/exit thresholds under controlled perturbation"
  "cross-over perturbation with washout/recovery, repeated whole-system panel and explicit history ledger"
  "no current cited IBS source is promoted as already proving hysteresis"

canonicalIBSTransitionParetoFrontier : List TransitionParetoNode
canonicalIBSTransitionParetoFrontier =
  flareDynamicsNode ∷ stressSymptomLagNode ∷ trajectoryPhenotypeNode ∷ hysteresisNode ∷ []

record IBSLatentStateTransitionBoundary : Set where
  constructor ibs-latent-state-transition-boundary
  field
    longitudinalEvidenceRetained : Bool
    individualSpecificTemporalStructureRetained : Bool
    symptomProjectionEqualsHiddenState : Bool
    lagAssociationEqualsCausalDirection : Bool
    trajectoryClusterEqualsAttractor : Bool
    flareRemissionDifferenceEqualsHysteresis : Bool
    historyAndPathMustRemainExplicit : Bool
    attractorLanguageRequiresValidationReceipt : Bool

canonicalIBSLatentStateTransitionBoundary : IBSLatentStateTransitionBoundary
canonicalIBSLatentStateTransitionBoundary = ibs-latent-state-transition-boundary
  true true false false false false true true
