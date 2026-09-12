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

------------------------------------------------------------------------
-- BIOACOUSTIC / FLY SNOWBALL + N-DIMENSIONAL PARETO BIDI FRONTIER
--
-- Thin specialization only. Attribution uses AttributedSourceCore; dependency
-- roles use TypedProvenanceDependencyGraphExact; Pareto ordering reuses the
-- arbitrary-axis CostHyperfabric through NDimParetoHyperfabricExact.
--
-- The stronger attribution/OSINT snowball invariants currently live on stacked
-- #873. Their governing rules are followed here without copying their types:
-- acquisition may be out of dependency order; identity/source role/scope stay
-- retained; citation creates neither proof nor authority; conclusion payment
-- may not skip an unpaid dependency.
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
  "primary method/source for the shared acoustic-manifold pipeline; external rows remain non-promoting"
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
  "primary experimental source for calcium recordings, auditory stimulus structure and data/code availability"
  Attr.publicAttribution

flyVRSource : Attr.AttributedSource
flyVRSource = Attr.mkNoDOISource
  "Murthy Lab"
  "FlyVR"
  "GitHub software repository"
  "2026"
  "https://github.com/murthylab/fly-vr"
  (Attr.namedSourceKind "primary software repository")
  "software identity for the stimulus presenter named by Gauthey et al.; not the exact run configuration"
  Attr.publicAttribution

sourceAtlas : Attr.AttributedSourceAtlas
sourceAtlas = Attr.mkSourceAtlas
  "bioacoustic / fly trajectory snowball sources"
  "DASHI.Biology.BioacousticFlySnowballParetoBidiExact"
  (areseSource ∷ gautheySource ∷ flyVRSource ∷ [])
  "identity/role atlas only; DOI/URL/source identity never imports proof, exact run identity, anatomical registration or authority"

------------------------------------------------------------------------
-- Leaves and paid history.
------------------------------------------------------------------------

data FrontierLeaf : Set where
  exactExternalManifest : FrontierLeaf
  sameTrialStimulusFunctionalTimebase : FrontierLeaf
  roiTrialPlaneIdentity : FrontierLeaf
  functionalToMaleCNSRegistration : FrontierLeaf
  rendererPolish : FrontierLeaf

leafReference : FrontierLeaf → String
leafReference exactExternalManifest =
  "exact external file/member manifest + content digest + source-role receipt"
leafReference sameTrialStimulusFunctionalTimebase =
  "auditory stimulus protocol/time axis <-> pooled functional time axis"
leafReference roiTrialPlaneIdentity =
  "pooled selected functional row -> exact source trial / plane / ROI-cluster identity"
leafReference functionalToMaleCNSRegistration =
  "functional source ROI -> exact MaleCNS neuron or explicitly candidate/unresolved registration"
leafReference rendererPolish =
  "additional aesthetic refinement after scientific carriers are inspectable"

data PaymentState : Set where
  unpaid : PaymentState
  sourceCodePaid : PaymentState
  exactSameObjectPaid : PaymentState

paymentState : FrontierLeaf → PaymentState
paymentState exactExternalManifest = unpaid
paymentState sameTrialStimulusFunctionalTimebase = sourceCodePaid
paymentState roiTrialPlaneIdentity = unpaid
paymentState functionalToMaleCNSRegistration = unpaid
paymentState rendererPolish = unpaid

paidTimebaseReference : String
paidTimebaseReference =
  "murthylab/lightbead-analysis: Fig3_aligment blob f34fe193f0507b5ad7f3c05d6b8973c04a34cf02 + fig3_preprocessing blob 39a4ae6739b9e13040b971469616e908df41f502; common 2P rate 2.20337115787 Hz, 668-sample truncation and 13-block protocol"

------------------------------------------------------------------------
-- Bidi snowball: evidence -> bounded claim; claim -> dependency reopening.
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
  paidTimebaseReference
  "the compact conventional-2P 668-sample carrier has the source-code-paid common aligned protocol time axis"
  "if the public alignment/preprocessing carrier changes or same-protocol identity is invalidated, reopen temporal response interpretations"
  true true true true false false

roiIdentityBidi : SnowballBidiReceipt
roiIdentityBidi = snowball-bidi-receipt
  roiTrialPlaneIdentity
  "four aligned source-trial dictionaries + source-equivalent global top-0.5% replay + exact compact 940x668 comparison"
  "on exact compact equality, pooled selected row may inherit exact source trial/plane/cluster identity"
  "without exact compact equality, replay remains a reconstruction candidate and pooled row identity stays unpaid"
  true true true true false false

registrationBidi : SnowballBidiReceipt
registrationBidi = snowball-bidi-receipt
  functionalToMaleCNSRegistration
  "functional anatomy / registration transform / structural target identity"
  "an exact or candidate functional-to-connectome registration may be carried with explicit identity status"
  "absence of exact registration reopens neuron identity; embedding proximity or source ROI identity cannot pay it"
  true true true true false false

------------------------------------------------------------------------
-- Typed provenance graph.
------------------------------------------------------------------------

gautheyFunctionalNode : Graph.DependencyNode
gautheyFunctionalNode = Graph.dependencyNode
  "Gauthey selected-ROI-by-time functional carrier"
  Graph.empiricalDataset
  "DOI 10.5281/zenodo.17618684; pooled 940 selected rows x 668 aligned samples"
  false

auditoryStimulusNode : Graph.DependencyNode
auditoryStimulusNode = Graph.dependencyNode
  "Gauthey auditory stimulus / source alignment carrier"
  Graph.runtimeAcquisition
  paidTimebaseReference
  false

alignedEpisodeNode : Graph.DependencyNode
alignedEpisodeNode = Graph.dependencyNode
  "protocol-aligned auditory-functional episode"
  Graph.dashiFormal
  "source-code-paid common time axis; not pooled-row identity, neuron identity or causality"
  false

rowIdentityNode : Graph.DependencyNode
rowIdentityNode = Graph.dependencyNode
  "pooled selected-row source identity"
  Graph.dashiFormal
  "candidate until source-equivalent replay is welded by exact array equality to the compact published carrier"
  false

maleCNSRegistrationNode : Graph.DependencyNode
maleCNSRegistrationNode = Graph.dependencyNode
  "functional-to-MaleCNS registration receipt"
  Graph.dashiFormal
  "exact/candidate/unresolved anatomical identity coordinate"
  false

stimulusAlignmentEdge : Graph.DependencyEdge
stimulusAlignmentEdge = Graph.dependencyEdge
  auditoryStimulusNode alignedEpisodeNode Graph.alignmentRole true
  "paid by inspected public alignment/preprocessing code for the common pooled time axis"

functionalAlignmentEdge : Graph.DependencyEdge
functionalAlignmentEdge = Graph.dependencyEdge
  gautheyFunctionalNode alignedEpisodeNode Graph.alignmentRole true
  "compact functional carrier uses the same 668-sample protocol-aligned time axis"

rowIdentityEdge : Graph.DependencyEdge
rowIdentityEdge = Graph.dependencyEdge
  gautheyFunctionalNode rowIdentityNode Graph.reconstructionRole true
  "requires four exact source-trial carriers, source-equivalent selection replay and exact compact-array equality"

registrationEdge : Graph.DependencyEdge
registrationEdge = Graph.dependencyEdge
  rowIdentityNode maleCNSRegistrationNode Graph.reconstructionRole true
  "source trial/plane/cluster identity is a prerequisite coordinate but does not itself establish MaleCNS neuron identity"

snowballDependencyGraph : Graph.TypedDependencyGraph
snowballDependencyGraph = Graph.typedDependencyGraph
  "bioacoustic/fly bidi snowball dependency graph"
  (gautheyFunctionalNode ∷ auditoryStimulusNode ∷ alignedEpisodeNode ∷
   rowIdentityNode ∷ maleCNSRegistrationNode ∷ [])
  (stimulusAlignmentEdge ∷ functionalAlignmentEdge ∷ rowIdentityEdge ∷
   registrationEdge ∷ [])

------------------------------------------------------------------------
-- N-dimensional Pareto specialization. Lower ordinal = lower debt/risk/cost.
-- Values are planning coordinates, never probabilities/truth/confidence.
------------------------------------------------------------------------

data FrontierAxis : Set where
  sameObjectDebt temporalAlignmentDebt provenanceDebt opportunityLoss
  identityRisk implementationCost : FrontierAxis

axisReference : FrontierAxis → String
axisReference sameObjectDebt = "unpaid same-object / carrier-identity debt"
axisReference temporalAlignmentDebt = "unpaid exact timebase/alignment debt"
axisReference provenanceDebt = "unpaid source/custody/digest/role provenance debt"
axisReference opportunityLoss = "scientific/diagnostic leverage lost if deferred"
axisReference identityRisk = "risk of accidental identity promotion without receipts"
axisReference implementationCost = "relative acquisition / implementation effort"

leafCost : FrontierAxis → FrontierLeaf → Nat
leafCost sameObjectDebt exactExternalManifest = 1
leafCost sameObjectDebt sameTrialStimulusFunctionalTimebase = 0
leafCost sameObjectDebt roiTrialPlaneIdentity = 0
leafCost sameObjectDebt functionalToMaleCNSRegistration = 0
leafCost sameObjectDebt rendererPolish = 4
leafCost temporalAlignmentDebt exactExternalManifest = 4
leafCost temporalAlignmentDebt sameTrialStimulusFunctionalTimebase = 0
leafCost temporalAlignmentDebt roiTrialPlaneIdentity = 0
leafCost temporalAlignmentDebt functionalToMaleCNSRegistration = 2
leafCost temporalAlignmentDebt rendererPolish = 4
leafCost provenanceDebt exactExternalManifest = 0
leafCost provenanceDebt sameTrialStimulusFunctionalTimebase = 0
leafCost provenanceDebt roiTrialPlaneIdentity = 0
leafCost provenanceDebt functionalToMaleCNSRegistration = 1
leafCost provenanceDebt rendererPolish = 3
leafCost opportunityLoss exactExternalManifest = 2
leafCost opportunityLoss sameTrialStimulusFunctionalTimebase = 0
leafCost opportunityLoss roiTrialPlaneIdentity = 0
leafCost opportunityLoss functionalToMaleCNSRegistration = 0
leafCost opportunityLoss rendererPolish = 4
leafCost identityRisk exactExternalManifest = 0
leafCost identityRisk sameTrialStimulusFunctionalTimebase = 0
leafCost identityRisk roiTrialPlaneIdentity = 1
leafCost identityRisk functionalToMaleCNSRegistration = 4
leafCost identityRisk rendererPolish = 0
leafCost implementationCost exactExternalManifest = 0
leafCost implementationCost sameTrialStimulusFunctionalTimebase = 0
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
  "application-declared ordinal axes; no scalar truth/alpha score"
  "highest-alpha unpaid evidence/acquisition leaf for the bioacoustic/fly programme"

frontierCosts : Pareto.CostHyperfabric frontierProblem
frontierCosts = Pareto.costHyperfabric FrontierAxis leafCost axisReference

frontierView : NDim.NDimParetoView frontierCosts
frontierView = NDim.ndimParetoView
  6
  "six explicitly declared debt/risk/cost axes"
  axisReference
  true
  "inspect non-dominated eligible leaves; do not collapse to one weighted score"

-- Paid timebase is retained in history but removed from the live unpaid list.
-- Registration remains live/non-dominated but is not the first execution target
-- because identity-risk and implementation-cost coordinates are much larger.
currentInspectionFrontier : List FrontierLeaf
currentInspectionFrontier =
  exactExternalManifest ∷
  roiTrialPlaneIdentity ∷
  functionalToMaleCNSRegistration ∷ []

firstExecutionLeaf : FrontierLeaf
firstExecutionLeaf = roiTrialPlaneIdentity

parallelAcquisitionLeaf : FrontierLeaf
parallelAcquisitionLeaf = exactExternalManifest

record SnowballParetoBoundary : Set where
  constructor snowball-pareto-boundary
  field
    acquisitionOrderEqualsPaymentOrder : Bool
    citationCreatesProof : Bool
    qidDeweyDOIOrURLCreatesAuthority : Bool
    paretoRequiresScalarScore : Bool
    lowestImplementationCostAutomaticallyWins : Bool
    paidLeafMustStayOnUnpaidFrontier : Bool
    forwardSupportDeletesReverseDependency : Bool
    visualOrEmbeddingSimilarityPaysIdentity : Bool
    multipleNonDominatedLeavesMayRemainLive : Bool
    unpaidDependencyMayReopenDownstreamClaim : Bool

canonicalSnowballParetoBoundary : SnowballParetoBoundary
canonicalSnowballParetoBoundary = snowball-pareto-boundary
  false false false false false false false false true true

snowballRulesOwner : String
snowballRulesOwner =
  "stacked #873: DASHI.Core.SnowballAttributionProvenanceInvariantExact + DASHI.Core.SnowballOSINTAcquisitionInvariantExact"

currentHighestAlphaReading : String
currentHighestAlphaReading =
  "The common Gauthey conventional-2P protocol timebase is source-code paid and removed from the unpaid frontier. First execute pooled-row source-identity recovery and require exact equality with the compact 940x668 carrier. Acquire exact external manifests/hashes in parallel. MaleCNS registration remains live but deferred by identity risk/cost; renderer polish is dominated for the current scientific consumer."
