module DASHI.Ontology.RosarioConceptualDiagnosticsExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport

------------------------------------------------------------------------
-- SOURCE / ATTRIBUTION BOUNDARY
--
-- Primary source:
--   Rosario Uceda-Sosa, Maria Chang,
--   Karthikeyan Natesan Ramamurthy, Moninder Singh,
--   "Conceptual Diagnostics for Knowledge Graphs and Large Language Models",
--   ACL 2025 Industry Track, pp. 531-540,
--   DOI 10.18653/v1/2025.acl-industry.37.
--
-- Prior paper explicitly cited by the ACL 2025 paper:
--   Uceda-Sosa et al.,
--   "Reasoning about concepts with LLMs: Inconsistencies abound",
--   COLM 2024.
--
-- Current OCTF/Wikidata continuation observed in 2026 meeting/course material:
--   Rosario's talk title is "Using LLM Semantic Failures to Analyze and
--   Improve Wikidata".  The current source formalisation below treats that as
--   continuation/context, not as if it were an additional theorem in the ACL
--   paper.
--
-- Everything in this file under `RosarioSourceClaim` records source claims.
-- DASHI owns the typed reconstruction, non-collapse statements, and authority
-- firewalls.  The source does not claim DASHI PNF, admissibility,
-- FactorsThrough, or our repair-governance constructions.
------------------------------------------------------------------------

data RosarioSourceClaim : Set where
  conceptualConsistencyDefinitionClaim : RosarioSourceClaim
  benchmarkFromConceptHierarchyClaim : RosarioSourceClaim
  boundedDomainSubgraphClaim : RosarioSourceClaim
  deductiveClosureAxiomTestsClaim : RosarioSourceClaim
  llmParaphraseClusterClaim : RosarioSourceClaim
  binaryAgreementClusterClaim : RosarioSourceClaim
  fourModelFamiliesEightDomainsClaim : RosarioSourceClaim
  overSixThousandEdgesThirtyThousandQueriesClaim : RosarioSourceClaim
  approximatelySevenToTenPercentInconsistencyClaim : RosarioSourceClaim
  approximatelyTwoPercentConsistentDisagreementClaim : RosarioSourceClaim
  falseNegativesDominateDisagreementClaim : RosarioSourceClaim
  hotspotDisagreementConcentrationClaim : RosarioSourceClaim
  kgNotDefinitiveGroundTruthClaim : RosarioSourceClaim
  llmConsensusCanSurfaceProblematicSubgraphsClaim : RosarioSourceClaim
  semiAutomatedKGRefinementClaim : RosarioSourceClaim
  openClosedWorldMismatchClaim : RosarioSourceClaim
  manualDomainSeedSelectionLimitationClaim : RosarioSourceClaim
  llmParaphraseBiasLimitationClaim : RosarioSourceClaim
  stochasticResponseLimitationClaim : RosarioSourceClaim

rosarioACL2025Source : Transport.SourceBackedClaim
rosarioACL2025Source = record
  { Transport.SourceClaim = RosarioSourceClaim
  ; Transport.sourceReceipt = benchmarkFromConceptHierarchyClaim
  ; Transport.sourceName = "Uceda-Sosa et al., Conceptual Diagnostics for Knowledge Graphs and Large Language Models"
  ; Transport.sourceLocator = "ACL 2025 Industry Track, 531-540, DOI 10.18653/v1/2025.acl-industry.37"
  ; Transport.reading = "source authority for the reported benchmark method, experiments, hotspot analysis and stated limitations; not authority for DASHI repair/admission semantics"
  }

------------------------------------------------------------------------
-- CONCEPTUAL HIERARCHY / AXIOM TEST SURFACE
--
-- The paper operationally treats concepts as sets of instances and uses a
-- subconcept hierarchy.  The five benchmark test families are represented as
-- source-method constructors.  This does not assert that Wikidata globally
-- satisfies these axioms or that absence in Wikidata is metaphysical negation.
------------------------------------------------------------------------

data ConceptAxiomTest : Set where
  edgeIdentityTest : ConceptAxiomTest
  benchmarkNegativeEdgeTest : ConceptAxiomTest
  strictInclusionTest : ConceptAxiomTest
  transitivityTest : ConceptAxiomTest
  propertyInheritanceTest : ConceptAxiomTest

data EdgePolarity : Set where
  positiveEdge : EdgePolarity
  negativeEdge : EdgePolarity

data ResponsePattern : Set where
  allYes : ResponsePattern
  allNo : ResponsePattern
  mixedYesNo : ResponsePattern

data ClusterClassification : Set where
  consistentAgreement : ClusterClassification
  consistentDisagreementFalsePositive : ClusterClassification
  consistentDisagreementFalseNegative : ClusterClassification
  conceptuallyInconsistent : ClusterClassification

classifyCluster : EdgePolarity → ResponsePattern → ClusterClassification
classifyCluster positiveEdge allYes = consistentAgreement
classifyCluster positiveEdge allNo = consistentDisagreementFalseNegative
classifyCluster positiveEdge mixedYesNo = conceptuallyInconsistent
classifyCluster negativeEdge allYes = consistentDisagreementFalsePositive
classifyCluster negativeEdge allNo = consistentAgreement
classifyCluster negativeEdge mixedYesNo = conceptuallyInconsistent

------------------------------------------------------------------------
-- EIGHT REPORTED WIKIDATA DOMAINS
------------------------------------------------------------------------

data BenchmarkDomain : Set where
  academicDisciplines : BenchmarkDomain
  dishes : BenchmarkDomain
  financeProducts : BenchmarkDomain
  homeAppliances : BenchmarkDomain
  medicalOccupations : BenchmarkDomain
  musicGenres : BenchmarkDomain
  naturalDisasters : BenchmarkDomain
  software : BenchmarkDomain

reportedDomains : List BenchmarkDomain
reportedDomains =
  academicDisciplines ∷
  dishes ∷
  financeProducts ∷
  homeAppliances ∷
  medicalOccupations ∷
  musicGenres ∷
  naturalDisasters ∷
  software ∷ []

------------------------------------------------------------------------
-- REPORTED MODEL FAMILIES
------------------------------------------------------------------------

data ModelFamily : Set where
  deepSeekFamily : ModelFamily
  llamaFamily : ModelFamily
  graniteFamily : ModelFamily
  mistralFamily : ModelFamily

reportedModelFamilies : List ModelFamily
reportedModelFamilies =
  deepSeekFamily ∷ llamaFamily ∷ graniteFamily ∷ mistralFamily ∷ []

------------------------------------------------------------------------
-- PIPELINE STAGES, FOLLOWING THE PAPER'S FIGURE/METHOD DESCRIPTION
------------------------------------------------------------------------

data BenchmarkStage : Set where
  extractBoundedDomainHierarchy : BenchmarkStage
  computeClosureAndTestEdges : BenchmarkStage
  generateCandidateParaphrases : BenchmarkStage
  insertDomainExamples : BenchmarkStage
  crossModelSemanticCheck : BenchmarkStage
  buildBinaryAgreementClusters : BenchmarkStage
  evaluateClusterResponses : BenchmarkStage
  aggregateEdgeDisagreement : BenchmarkStage
  surfaceProblematicSubgraphs : BenchmarkStage

data StageStep : BenchmarkStage → BenchmarkStage → Set where
  s1 : StageStep extractBoundedDomainHierarchy computeClosureAndTestEdges
  s2 : StageStep computeClosureAndTestEdges generateCandidateParaphrases
  s3 : StageStep generateCandidateParaphrases insertDomainExamples
  s4 : StageStep insertDomainExamples crossModelSemanticCheck
  s5 : StageStep crossModelSemanticCheck buildBinaryAgreementClusters
  s6 : StageStep buildBinaryAgreementClusters evaluateClusterResponses
  s7 : StageStep evaluateClusterResponses aggregateEdgeDisagreement
  s8 : StageStep aggregateEdgeDisagreement surfaceProblematicSubgraphs

------------------------------------------------------------------------
-- PARAPHRASE SEMANTICS: GENERATED != VERIFIED EQUIVALENCE
--
-- The source itself uses cross-model/domain checks to support its paraphrase
-- clusters.  We therefore preserve a candidate/admitted distinction rather
-- than treating an LLM-generated rewording as semantically equivalent by fiat.
------------------------------------------------------------------------

data ParaphraseState : Set where
  generatedCandidate : ParaphraseState
  domainCheckedParaphrase : ParaphraseState

data SemanticEquivalencePermission : ParaphraseState → Set where
  checkedParaphraseMayEnterBenchmark :
    SemanticEquivalencePermission domainCheckedParaphrase

generatedParaphraseCannotAssertEquivalence :
  SemanticEquivalencePermission generatedCandidate → ⊥
generatedParaphraseCannotAssertEquivalence ()

------------------------------------------------------------------------
-- WIKIDATA / WORLD AUTHORITY FIREWALLS
--
-- Section 5 explicitly says community-curated KGs such as Wikidata cannot be
-- treated as definitive ground truth.  Section 7/8 also discusses the semantic
-- mismatch between KG closed-world benchmark assumptions and open-world LLM
-- behaviour.  We preserve those boundaries literally.
------------------------------------------------------------------------

data KGGroundTruthPromotionPermission : Set where

kgCannotPromoteItselfToGroundTruth : KGGroundTruthPromotionPermission → ⊥
kgCannotPromoteItselfToGroundTruth ()

data EdgeAbsenceNegationPromotionPermission : Set where

absenceCannotBecomeNegationOutsideBenchmarkConvention :
  EdgeAbsenceNegationPromotionPermission → ⊥
absenceCannotBecomeNegationOutsideBenchmarkConvention ()

------------------------------------------------------------------------
-- LLM CONSENSUS / HOTSPOT AUTHORITY FIREWALLS
--
-- The paper uses disagreement/consensus as a diagnostic signal and proposes it
-- as a complement to symbolic curation.  It does not establish that model
-- consensus is ontology truth or that a hotspot authorizes a Wikidata edit.
------------------------------------------------------------------------

data LLMConsensusTruthPermission : Set where

data LLMHotspotEditPermission : Set where

llmConsensusCannotAssertOntologyTruth : LLMConsensusTruthPermission → ⊥
llmConsensusCannotAssertOntologyTruth ()

llmHotspotCannotAuthorizeEdit : LLMHotspotEditPermission → ⊥
llmHotspotCannotAuthorizeEdit ()

------------------------------------------------------------------------
-- HOTSPOT / REFINEMENT SURFACE
------------------------------------------------------------------------

data HotspotSignal : Set where
  consistentClusterDisagreement : HotspotSignal
  highEdgeDisagreementRate : HotspotSignal
  crossModelConcentratedDisagreement : HotspotSignal

data HotspotDisposition : Set where
  diagnosticOnly : HotspotDisposition
  needsHumanAttention : HotspotDisposition
  candidateForSymbolicReview : HotspotDisposition

record HotspotObservation : Set where
  constructor hotspotObservation
  field
    domain : BenchmarkDomain
    signal : HotspotSignal
    disposition : HotspotDisposition
    sourceReference : String

open HotspotObservation public

------------------------------------------------------------------------
-- SOURCE-REPORTED EMPIRICAL RESULTS REMAIN SOURCE RECEIPTS
------------------------------------------------------------------------

record ReportedEmpiricalProfile : Set where
  constructor reportedEmpiricalProfile
  field
    modelFamilyCount : Nat
    domainCount : Nat
    queryCountLowerBound : Nat
    deducibleEdgeCountLowerBound : Nat
    resultReference : String

open ReportedEmpiricalProfile public

acl2025ReportedProfile : ReportedEmpiricalProfile
acl2025ReportedProfile =
  reportedEmpiricalProfile
    4
    8
    30000
    6000
    "ACL 2025 paper reports four model families, eight domains, over 30,000 queries and over 6,000 deducible edges"

------------------------------------------------------------------------
-- SOURCE CLAIM != LOCAL THEOREM
------------------------------------------------------------------------

data RosarioSourcePromotionPermission : Set where

rosarioSourceCannotPromoteRepoTheorem : RosarioSourcePromotionPermission → ⊥
rosarioSourceCannotPromoteRepoTheorem ()

------------------------------------------------------------------------
-- ATTRIBUTION SPLIT
------------------------------------------------------------------------

data AttributionOwner : Set where
  rosarioAndCoauthors : AttributionOwner
  octfMeetingRecord : AttributionOwner
  sensiblawPriorArtNote : AttributionOwner
  dashiReconstruction : AttributionOwner

data FormalLayer : Set where
  reportedBenchmarkMethod : FormalLayer
  reportedEmpiricalFinding : FormalLayer
  reportedKGRefinementDirection : FormalLayer
  localTypedNonCollapse : FormalLayer
  localRepairGovernance : FormalLayer

ownerOf : FormalLayer → AttributionOwner
ownerOf reportedBenchmarkMethod = rosarioAndCoauthors
ownerOf reportedEmpiricalFinding = rosarioAndCoauthors
ownerOf reportedKGRefinementDirection = rosarioAndCoauthors
ownerOf localTypedNonCollapse = dashiReconstruction
ownerOf localRepairGovernance = dashiReconstruction

------------------------------------------------------------------------
-- STATUS RECEIPT
------------------------------------------------------------------------

record RosarioConceptualDiagnosticsStatus : Set where
  constructor rosarioConceptualDiagnosticsStatus
  field
    sourceClaimsRemainBounded : Bool
    benchmarkPipelineRepresented : Bool
    binaryAgreementClassificationRepresented : Bool
    generatedParaphraseNotAutoEquivalent : Bool
    wikidataNotPromotedToGroundTruth : Bool
    absenceNotPromotedToGenericNegation : Bool
    llmConsensusNotPromotedToTruth : Bool
    llmHotspotNotEditAuthority : Bool
    diagnosticAndRepairDirectionsSeparated : Bool
    limitationsRepresented : Bool

    sourceClaimsRemainBoundedIsTrue : sourceClaimsRemainBounded ≡ true
    benchmarkPipelineRepresentedIsTrue : benchmarkPipelineRepresented ≡ true
    binaryAgreementClassificationRepresentedIsTrue :
      binaryAgreementClassificationRepresented ≡ true
    generatedParaphraseNotAutoEquivalentIsTrue :
      generatedParaphraseNotAutoEquivalent ≡ true
    wikidataNotPromotedToGroundTruthIsTrue :
      wikidataNotPromotedToGroundTruth ≡ true
    absenceNotPromotedToGenericNegationIsTrue :
      absenceNotPromotedToGenericNegation ≡ true
    llmConsensusNotPromotedToTruthIsTrue : llmConsensusNotPromotedToTruth ≡ true
    llmHotspotNotEditAuthorityIsTrue : llmHotspotNotEditAuthority ≡ true
    diagnosticAndRepairDirectionsSeparatedIsTrue :
      diagnosticAndRepairDirectionsSeparated ≡ true
    limitationsRepresentedIsTrue : limitationsRepresented ≡ true

open RosarioConceptualDiagnosticsStatus public

canonicalRosarioConceptualDiagnosticsStatus : RosarioConceptualDiagnosticsStatus
canonicalRosarioConceptualDiagnosticsStatus =
  rosarioConceptualDiagnosticsStatus
    true true true true true true true true true true
    refl refl refl refl refl refl refl refl refl refl
