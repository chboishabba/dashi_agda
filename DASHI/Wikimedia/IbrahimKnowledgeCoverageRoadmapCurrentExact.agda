module DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapCurrentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapExact as Historical
import DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapDeltaExact as Delta
import DASHI.Wikimedia.IbrahimSnowballMemoryRepetitionSourceDependencyConsensusBidiExact as Dependency
import DASHI.Wikimedia.IbrahimSnowballEvidenceSynthesisPeerReviewConflictIndependenceBidiExact as Synthesis
import DASHI.Wikimedia.IbrahimSnowballDependencyNDimLocalGlobalProofSearchBidiExact as NDim
import DASHI.Wikimedia.IbrahimSnowballAtomicClaimIntentExperimentAdequacyBidiExact as Atomic
import DASHI.Wikimedia.IbrahimSnowballEthnographyParticipantObservationFieldworkBidiExact as Fieldwork
import DASHI.Wikimedia.IbrahimSnowballGeologyStratigraphyDeepTimeCarbonConsumerBidiExact as Geology
import DASHI.Wikimedia.IbrahimSnowballHealthcareAccessQualityEfficacyConsumerBidiExact as Healthcare
import DASHI.Wikimedia.IbrahimSnowballPetrochemistryLifecycleParentAuditExact as Petrochem
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey

data LiveState : Set where
  completeAsParent : LiveState
  residualOnly : LiveState
  concreteConsumerNeeded : LiveState
  compositionNeeded : LiveState

record LiveRoadmapTarget : Set where
  constructor live-roadmap-target
  field
    rank : Nat
    target : String
    state : LiveState
    alreadyPaidBy : String
    remaining : String
    qidCoordinate : String
    deweyCoordinate : String
    sourceCoordinate : String
    completionTest : String
open LiveRoadmapTarget public

independenceConsensusNowPaid : LiveRoadmapTarget
independenceConsensusNowPaid = live-roadmap-target
  0
  "Corroboration / replication / common-source dependence / evidence synthesis / peer review / consensus"
  completeAsParent
  "LearningMemoryTraumaReplicationConsensus; MemoryRepetitionSourceDependencyConsensus; EvidenceSynthesisPeerReviewConflictIndependence"
  "only consumer-specific source-dependency calculations remain"
  "reproducibility Q1425625; scientific consensus Q316748; systematic review Q1504425; meta-analysis Q815382; peer review Q215028; conflict of interest Q211067"
  "unresolved where no exact inspected DDC is paid"
  "DOI-bounded independence/evidence-synthesis sources travel with local owners"
  "future work must exhibit a concrete dependence structure not representable by the shared provenance grammar"

atomicExperimentAdequacyNowPaid : LiveRoadmapTarget
atomicExperimentAdequacyNowPaid = live-roadmap-target
  0
  "Human intent / atomic claim / operationalization / experiment / exact consumer"
  completeAsParent
  "DependencyNDimLocalGlobalProofSearch; AtomicClaimIntentExperimentAdequacy"
  "only domain-specific specification mismatches remain"
  "scientific hypothesis Q3144351; scientific method Q46857; operationalization Q286017"
  "no forced DDC for construct validity/operationalization"
  "Blackwell 1953 DOI 10.1214/aoms/1177729032; Cronbach-Meehl 1955 DOI 10.1037/h0040957"
  "green tests cannot be promoted unless constructor, operationalization and tested consumer match the intended atomic claim"

ethnographyParticipantObservation : LiveRoadmapTarget
ethnographyParticipantObservation = live-roadmap-target
  0
  "Ethnography / participant observation"
  completeAsParent
  "EthnographyParticipantObservationFieldworkBidiExact plus Two-Eyed/community observer, consent/coercion, archive/source criticism and testimony/credibility owners"
  "only concrete fieldwork-specific residuals remain"
  "ethnography Q132151; participant observation Q1129049"
  "DDC unresolved until an exact inspected classification is paid"
  "Roque et al. DOI 10.1177/1525822X231198989; Seim DOI 10.1177/0049124120986209; Brear-Tsotetsi DOI 10.1177/14687941211004417"
  "future work must exhibit an observer/participant/consent/authority/source-provenance distinction not representable by the canonical fieldwork receipt"

geologyBreadthNowPaid : LiveRoadmapTarget
geologyBreadthNowPaid = live-roadmap-target
  0
  "Geology / stratigraphy concrete deep-time-carbon consumer"
  completeAsParent
  "GeologyStratigraphyDeepTimeCarbonConsumerBidiExact plus DeepTimeCarbonReservoirFluxBalance and LESDomainBasisBidiFrontier"
  "only consumer-specific petrology/geophysics/weathering/tectonic calculations remain; do not expand taxonomy without a real downstream consumer"
  "geology Q1069; Earth science Q8008; stratigraphy Q134783; sedimentology Q205768; geomorphology Q52109; tectonics Q193343; stratigraphic unit Q3694119"
  "geology Q1069 carries inspected DDC 550 and 551; subdiscipline DDCs remain unresolved until individually inspected"
  "Leithold-Blair-Wegmann DOI 10.1016/j.earscirev.2015.10.011; Romans-Graham DOI 10.1146/annurev-marine-121211-172426; Liang et al. DOI 10.1016/j.earscirev.2025.105312"
  "future geology work must exhibit a concrete distinction not representable by stock/source/transport/deposition/preservation/stratigraphic-context grammar"

healthcareBreadthNowPaid : LiveRoadmapTarget
healthcareBreadthNowPaid = live-roadmap-target
  0
  "Healthcare / public-health concrete access-quality-efficacy consumer"
  completeAsParent
  "HealthcareAccessQualityEfficacyConsumerBidiExact plus HealthcareEqualityInvariant and HealthcareAccessDistortion"
  "only consumer-specific clinical-efficacy, service-delivery, population-effect or governance calculations remain; do not collapse them into access"
  "health care Q31207; public health Q189603; health care quality Q17003063; health equity Q1512929; health services research Q5691150; universal health care Q3274205; health service Q9353606"
  "medical/library classification remains navigation only; DDCs unresolved until exact inspection"
  "WHO Universal Health Coverage institutional source; Kruk et al. DOI 10.1016/S2214-109X(18)30386-3"
  "future healthcare work must exhibit a distinction not representable by need/efficacy/access/coverage/quality/affordability/equity/population-impact grammar"

petrochemistryParentNowPaid : LiveRoadmapTarget
petrochemistryParentNowPaid = live-roadmap-target
  0
  "Petrochemistry / petroleum / refining / materials / emissions lifecycle"
  completeAsParent
  "PetrochemistryLifecycleParentAuditExact; SaltPetroleumIndustrialChemistryNetwork; DeepTimeCarbonBiosphereFossilFuel"
  "only process- or product-specific feed identity, plant validation, material balance and quantitative emissions receipts remain"
  "petrochemistry Q493630; petroleum Q22656; steam cracking Q2335334; cracking Q212749"
  "petrochemistry DDC unresolved; chemistry/engineering shelf choice remains navigation only"
  "Gholami et al. DOI 10.3390/en14238190; Sadrameli DOI 10.1016/j.fuel.2014.09.034 plus existing institutional process sources"
  "future petrochemistry work must exhibit a lifecycle/process distinction not representable by geological reservoir -> extraction/feed -> process transformation -> product -> combustion/surface-carbon-return grammar"

record RoadmapCompletionCriterion : Set where
  constructor roadmap-completion-criterion
  field
    parentJointsRepresented : Bool
    qidAcquisitionPolicyPresent : Bool
    deweyIsNavigationOnly : Bool
    doiSourceRoleIsIndependentCoordinate : Bool
    provenanceIndependenceRepresented : Bool
    consumerAdequacyRepresented : Bool
    remainingBreadthIsConsumerDriven : Bool
    knownSharedParentResidualsRemain : Bool
    roadmapMeansEveryPossibleTopicFormalised : Bool
open RoadmapCompletionCriterion public

currentRoadmapCriterion : RoadmapCompletionCriterion
currentRoadmapCriterion = roadmap-completion-criterion
  true true true true true true true false false

roadmapMeaning : String
roadmapMeaning =
  "roadmap completion means the shared navigation/provenance/consumer grammar can route new concrete demands to an existing owner or expose one typed residual; no known shared-parent residual remains in the current audit. It does not mean pre-enumerating every Dewey subject, QID, DOI, discipline or empirical claim."

historicalPolicy : Historical.RoadmapPolicy
historicalPolicy = Historical.canonicalRoadmapPolicy

deltaPolicy : Delta.RoadmapDeltaPolicy
deltaPolicy = Delta.canonicalRoadmapDeltaPolicy

independenceBoundary : Synthesis.EvidenceSynthesisPeerReviewIndependenceBoundary
independenceBoundary = Synthesis.canonicalEvidenceSynthesisPeerReviewIndependenceBoundary

atomicBoundary : Atomic.AtomicClaimIntentExperimentAdequacyBoundary
atomicBoundary = Atomic.canonicalAtomicClaimIntentExperimentAdequacyBoundary

fieldworkBoundary : Fieldwork.EthnographyParticipantObservationBoundary
fieldworkBoundary = Fieldwork.canonicalEthnographyParticipantObservationBoundary

geologyBoundary : Geology.GeologyStratigraphyDeepTimeCarbonBoundary
geologyBoundary = Geology.canonicalGeologyStratigraphyDeepTimeCarbonBoundary

healthcareBoundary : Healthcare.HealthcareAccessQualityEfficacyBoundary
healthcareBoundary = Healthcare.canonicalHealthcareAccessQualityEfficacyBoundary

petrochemistryBoundary : Petrochem.PetrochemistryParentAuditBoundary
petrochemistryBoundary = Petrochem.canonicalPetrochemistryParentAuditBoundary
