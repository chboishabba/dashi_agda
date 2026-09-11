module DASHI.Biology.BioacousticFlySnowballParetoBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.TypedProvenanceDependencyGraphExact as Graph
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Biology.BioacousticAreseSharedManifoldProducerExact as Arese
import DASHI.Biology.DrosophilaGautheyFunctionalTrajectoryProducerExact as Gauthey

------------------------------------------------------------------------
-- BIOACOUSTIC / FLY SNOWBALL + N-DIMENSIONAL PARETO BIDI FRONTIER
--
-- This is a thin application specialization over existing repo-native owners:
--   * AttributedSourceCore for author/title/publication/DOI/source-role;
--   * TypedProvenanceDependencyGraphExact for typed dependency edges;
--   * NDimParetoHyperfabricExact for arbitrary-axis non-scalar Pareto order.
--
-- The stronger SnowballAttributionProvenanceInvariantExact and
-- SnowballOSINTAcquisitionInvariantExact currently live on the stacked #873
-- branch.  This owner follows their exact rules without copying their
-- machinery into this branch: acquisition may be out of dependency order;
-- identity, source role and proposition scope stay retained; citation does not
-- import proof or authority; conclusion payment may not skip an unpaid leaf.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Source attribution.  DOI / URL are identity-navigation coordinates only.
------------------------------------------------------------------------

areseSource : Attr.AttributedSource
areseSource = Attr.mkDOISource
  "Lucio Arese"
  "Shared acoustic manifolds for exploratory comparison of passerine vocalizations"
  "EcoEvoRxiv, version 4"
  "2026"
  "10.32942/X2W65N"
  "https://ecoevorxiv.org/repository/view/11548/"
  Attr.academicArticleSource
  "primary method/source for the published shared acoustic-manifold pipeline; does not promote external rows into Animalexic canonical state"
  Attr.publicAttribution

gautheySource : Attr.AttributedSource
gautheySource = Attr.mkDOISource
  "Wayan Gauthey; Albert Lin; Osama M. Ahmed; Andrew M. Leifer; Mala Murthy; Stephan Y. Thiberge et al."
  "High-speed whole-brain imaging in Drosophila"
  "Nature Communications 17"
  "2026"
  "10.1038/s41467-026-72437-1"
  "https://doi.org/10.1038/s41467-026-72437-1"
  Attr.academicArticleSource
  "primary experimental source for whole-brain/central-brain calcium recordings, auditory stimulus structure, pulse-resolved analysis and data/code availability"
  Attr.publicAttribution

flyVRSource : Attr.AttributedSource
flyVRSource = Attr.mkNoDOISource
  "Murthy Lab"
  "FlyVR"
  "GitHub software repository"
  "2026"
  "https://github.com/murthylab/fly-vr"
  (Attr.namedSourceKind "primary software repository")
  "primary software-identity coordinate for the auditory stimulus presenter named by Gauthey et al.; repository identity is not the exact experiment-run configuration"
  Attr.publicAttribution

sourceAtlas : Attr.AttributedSourceAtlas
sourceAtlas = Attr.mkSourceAtlas
  "bioacoustic / fly trajectory snowball sources"
  "DASHI.Biology.BioacousticFlySnowballParetoBidiExact"
  (areseSource ∷ gautheySource ∷ flyVRSource ∷ [])
  "source identity and source role for the current highest-alpha trajectory/alignment frontier; citation never imports proof, experiment identity, exact run configuration or anatomical registration"

------------------------------------------------------------------------
-- Unpaid leaves.  These are acquisition/proof-search targets, not claims that
-- the corresponding evidence already exists.
------------------------------------------------------------------------

data FrontierLeaf : Set where
  exactExternalManifest : FrontierLeaf
  sameTrialStimulusFunctionalTimebase : FrontierLeaf
  roiTrialPlaneIdentity : FrontierLeaf
  functionalToMaleCNSRegistration : FrontierLeaf
  rendererPolish : FrontierLeaf

leafReference : FrontierLeaf → String
leafReference exactExternalManifest =
  "exact external source-file/member manifest + content digest + source-role receipt"
leafReference sameTrialStimulusFunctionalTimebase =
  "same-trial auditory stimulus clock <-> functional imaging clock alignment"
leafReference roiTrialPlaneIdentity =
  "selected functional row -> exact source trial / plane / ROI-cluster identity"
leafReference functionalToMaleCNSRegistration =
  "functional source ROI -> exact MaleCNS neuron or typed unresolved/candidate registration"
leafReference rendererPolish =
  "additional aesthetic / renderer refinement after scientific carriers are already inspectable"

------------------------------------------------------------------------
-- Bidi snowball: forward evidence -> bounded claim support, reverse claim ->
-- exact dependency that must be reopened if unpaid or invalidated.
------------------------------------------------------------------------

record SnowballBidiReceipt : Set where
  constructor snowball-bidi-receipt
  field
    leaf : FrontierLeaf
    forwardEvidenceReference : String
    forwardBoundedClaimReference : String
    reverseDependencyReference : String
    sourceIdentityRetained : Bool
    sourceRoleRetained : Bool
    sameObjectStatusRetained : Bool
    acquisitionMayOccurBeforePayment : Bool
    paymentMaySkipUnpaidDependency : Bool
    citationCreatesAuthority : Bool

open SnowballBidiReceipt public

sameTrialTimebaseBidi : SnowballBidiReceipt
sameTrialTimebaseBidi = snowball-bidi-receipt
  sameTrialStimulusFunctionalTimebase
  "Gauthey experiment data + Data/Stimulus / FlyVR-produced auditory carrier + functional trial timestamps"
  "a declared stimulus event may be aligned to a declared functional sample interval on the same trial"
  "if trial identity, clock origin, sample timing or stimulus-event identity is unpaid, reopen this alignment before any lag/response inference"
  true true true true false false

roiIdentityBidi : SnowballBidiReceipt
roiIdentityBidi = snowball-bidi-receipt
  roiTrialPlaneIdentity
  "source preprocessing indices / per-trial ROI extraction metadata"
  "a selected pooled row may recover its exact source trial/plane/ROI identity"
  "without the source-selection index crosswalk, pooled row number remains only a pooled selected-row identity"
  true true true true false false

registrationBidi : SnowballBidiReceipt
registrationBidi = snowball-bidi-receipt
  functionalToMaleCNSRegistration
  "functional anatomy / registration transform / structural target identity"
  "an exact or candidate functional-to-connectome registration can be carried with explicit identity status"
  "absence of an exact same-object registration receipt reopens neuron identity; embedding proximity or cell-class similarity cannot pay it"
  true true true true false false

------------------------------------------------------------------------
-- Typed provenance graph: forward carriers and reverse dependencies use the
-- same nodes.  An edge role is not an authority weight.
------------------------------------------------------------------------

areseDatasetNode : Graph.DependencyNode
areseDatasetNode = Graph.dependencyNode
  "Arese Zenodo shared-manifold CSV carrier"
  Graph.empiricalDataset
  "published external frame-level descriptor/embedding outputs; DOI 10.5281/zenodo.18332166"
  false

gautheyFunctionalNode : Graph.DependencyNode
gautheyFunctionalNode = Graph.dependencyNode
  "Gauthey selected-ROI-by-time functional carrier"
  Graph.empiricalDataset
  "preprocessed selected ROI x time object; DOI 10.5281/zenodo.17618684"
  false

auditoryStimulusNode : Graph.DependencyNode
auditoryStimulusNode = Graph.dependencyNode
  "Gauthey auditory stimulus/event carrier"
  Graph.runtimeAcquisition
  "stimulus sequence/event times delivered by FlyVR in the same experimental programme"
  false

alignedEpisodeNode : Graph.DependencyNode
alignedEpisodeNode = Graph.dependencyNode
  "same-trial aligned auditory-functional episode"
  Graph.dashiFormal
  "candidate same-object temporal weld; not neuron identity or causal mechanism"
  false

maleCNSRegistrationNode : Graph.DependencyNode
maleCNSRegistrationNode = Graph.dependencyNode
  "functional-to-MaleCNS registration receipt"
  Graph.dashiFormal
  "exact/candidate/unresolved structural identity coordinate"
  false

stimulusAlignmentEdge : Graph.DependencyEdge
stimulusAlignmentEdge = Graph.dependencyEdge
  auditoryStimulusNode alignedEpisodeNode Graph.alignmentRole true
  "required same-trial stimulus/timebase input; temporal adjacency alone is insufficient"

functionalAlignmentEdge : Graph.DependencyEdge
functionalAlignmentEdge = Graph.dependencyEdge
  gautheyFunctionalNode alignedEpisodeNode Graph.alignmentRole true
  "required functional time-series input on the same trial/timebase"

registrationDependsOnAlignedEpisode : Graph.DependencyEdge
registrationDependsOnAlignedEpisode = Graph.dependencyEdge
  alignedEpisodeNode maleCNSRegistrationNode Graph.reconstructionRole false
  "alignment is useful context for registration but does not itself establish neuron identity"

snowballDependencyGraph : Graph.TypedDependencyGraph
snowballDependencyGraph = Graph.typedDependencyGraph
  "bioacoustic/fly bidi snowball dependency graph"
  (areseDatasetNode ∷ gautheyFunctionalNode ∷ auditoryStimulusNode ∷
   alignedEpisodeNode ∷ maleCNSRegistrationNode ∷ [])
  (stimulusAlignmentEdge ∷ functionalAlignmentEdge ∷
   registrationDependsOnAlignedEpisode ∷ [])

------------------------------------------------------------------------
-- N-dimensional Pareto specialization.
--
-- All axes are costs/debts: lower is preferred.  The values are explicit
-- planning ordinals, not probabilities, confidence, scientific truth or
-- empirical effect sizes.  No weighted scalar score is defined.
------------------------------------------------------------------------

data FrontierAxis : Set where
  sameObjectDebt temporalAlignmentDebt provenanceDebt opportunityLoss
  identityRisk implementationCost : FrontierAxis

axisReference : FrontierAxis → String
axisReference sameObjectDebt = "unpaid same-object / carrier-identity debt"
axisReference temporalAlignmentDebt = "unpaid exact timebase/alignment debt"
axisReference provenanceDebt = "unpaid source/custody/digest/role provenance debt"
axisReference opportunityLoss = "scientific/diagnostic leverage lost if this leaf is deferred"
axisReference identityRisk = "risk of accidental identity promotion if pursued without receipts"
axisReference implementationCost = "relative acquisition / implementation effort"

leafCost : FrontierAxis → FrontierLeaf → Nat
leafCost sameObjectDebt exactExternalManifest = 1
leafCost sameObjectDebt sameTrialStimulusFunctionalTimebase = 1
leafCost sameObjectDebt roiTrialPlaneIdentity = 0
leafCost sameObjectDebt functionalToMaleCNSRegistration = 0
leafCost sameObjectDebt rendererPolish = 4
leafCost temporalAlignmentDebt exactExternalManifest = 4
leafCost temporalAlignmentDebt sameTrialStimulusFunctionalTimebase = 0
leafCost temporalAlignmentDebt roiTrialPlaneIdentity = 2
leafCost temporalAlignmentDebt functionalToMaleCNSRegistration = 3
leafCost temporalAlignmentDebt rendererPolish = 4
leafCost provenanceDebt exactExternalManifest = 0
leafCost provenanceDebt sameTrialStimulusFunctionalTimebase = 1
leafCost provenanceDebt roiTrialPlaneIdentity = 0
leafCost provenanceDebt functionalToMaleCNSRegistration = 1
leafCost provenanceDebt rendererPolish = 3
leafCost opportunityLoss exactExternalManifest = 2
leafCost opportunityLoss sameTrialStimulusFunctionalTimebase = 0
leafCost opportunityLoss roiTrialPlaneIdentity = 1
leafCost opportunityLoss functionalToMaleCNSRegistration = 0
leafCost opportunityLoss rendererPolish = 4
leafCost identityRisk exactExternalManifest = 0
leafCost identityRisk sameTrialStimulusFunctionalTimebase = 0
leafCost identityRisk roiTrialPlaneIdentity = 1
leafCost identityRisk functionalToMaleCNSRegistration = 4
leafCost identityRisk rendererPolish = 0
leafCost implementationCost exactExternalManifest = 0
leafCost implementationCost sameTrialStimulusFunctionalTimebase = 1
leafCost implementationCost roiTrialPlaneIdentity = 2
leafCost implementationCost functionalToMaleCNSRegistration = 4
leafCost implementationCost rendererPolish = 1

frontierProblem : Pareto.ConsumerMDLProblem
frontierProblem = Pareto.consumerMDLProblem
  FrontierLeaf
  (λ _ → ⊤)
  (λ _ → ⊤)
  (leafCost implementationCost)
  _≡_
  leafReference
  "ordinal costs are application-declared planning coordinates; no scalar truth score"
  "highest-alpha unpaid evidence/acquisition leaf for the bioacoustic/fly programme"

frontierCosts : Pareto.CostHyperfabric frontierProblem
frontierCosts = Pareto.costHyperfabric FrontierAxis leafCost axisReference

frontierView : NDim.NDimParetoView frontierCosts
frontierView = NDim.ndimParetoView
  6
  "six explicitly declared debt/risk/cost axes"
  axisReference
  true
  "inspect the non-dominated leaves directly; do not collapse to one weighted alpha score"

-- The current inspection frontier deliberately retains multiple non-dominated
-- leaves.  This list is navigational; Pareto admissibility remains the typed
-- relation from NDimParetoHyperfabricExact rather than a hard-coded winner.
currentInspectionFrontier : List FrontierLeaf
currentInspectionFrontier =
  exactExternalManifest ∷
  sameTrialStimulusFunctionalTimebase ∷
  roiTrialPlaneIdentity ∷
  functionalToMaleCNSRegistration ∷ []

record SnowballParetoBoundary : Set where
  constructor snowball-pareto-boundary
  field
    acquisitionOrderEqualsPaymentOrder : Bool
    citationCreatesProof : Bool
    qidDeweyDOIOrURLCreatesAuthority : Bool
    paretoRequiresScalarScore : Bool
    lowestImplementationCostAutomaticallyWins : Bool
    forwardSupportDeletesReverseDependency : Bool
    visualOrEmbeddingSimilarityPaysIdentity : Bool
    multipleNonDominatedLeavesMayRemainLive : Bool
    unpaidDependencyMayReopenDownstreamClaim : Bool

canonicalSnowballParetoBoundary : SnowballParetoBoundary
canonicalSnowballParetoBoundary = snowball-pareto-boundary
  false false false false false false false true true

------------------------------------------------------------------------
-- Cross-owner receipts retained as navigation, not proof promotion.
------------------------------------------------------------------------

areseProducerOwner : String
areseProducerOwner =
  "DASHI.Biology.BioacousticAreseSharedManifoldProducerExact"

gautheyProducerOwner : String
gautheyProducerOwner =
  "DASHI.Biology.DrosophilaGautheyFunctionalTrajectoryProducerExact"

snowballRulesOwner : String
snowballRulesOwner =
  "stacked #873: DASHI.Core.SnowballAttributionProvenanceInvariantExact + DASHI.Core.SnowballOSINTAcquisitionInvariantExact"

currentHighestAlphaReading : String
currentHighestAlphaReading =
  "Pay same-trial auditory-stimulus/function timebase and pooled-row source identity before attempting exact MaleCNS neuron registration. Acquire external manifests/hashes opportunistically in parallel. Keep registration live but high-risk; renderer polish is not a scientific dependency."
