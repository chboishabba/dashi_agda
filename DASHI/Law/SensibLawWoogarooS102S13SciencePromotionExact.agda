module DASHI.Law.SensibLawWoogarooS102S13SciencePromotionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.EvidenceProvenanceDependencyDagExact as Provenance
import DASHI.Law.SensibLawWoogarooKoalaScienceSnowballExact as Science
import DASHI.Law.SensibLawWoogarooEvidenceDependencyMatrixExact as Dependency
import DASHI.Law.SensibLawWoogarooS102LikelySignificantDetrimentalEffectCaseExact as S102
import DASHI.Law.SensibLawWoogarooS13EssentialityStressTestExact as S13
import DASHI.Law.SensibLawWoogarooEPBC43BHistoricalClearingApplicabilityExact as S43B

------------------------------------------------------------------------
-- SCIENCE -> LEGAL CONSUMER PROMOTION
--
-- State-of-the-art science can pay mechanism/method propositions.  It cannot
-- silently pay same-object Springview facts, statutory conclusions, Ministerial
-- opinions, or the existence/application of an exemption.
------------------------------------------------------------------------

data LegalConsumer : Set where
  s102ThreateningProcess : LegalConsumer
  s102LikelySignificantDetrimentalEffect : LegalConsumer
  s13ViablePopulationIdentity : LegalConsumer
  s13Essentiality : LegalConsumer
  s43BApplicability : LegalConsumer

data EvidenceRole : Set where
  statutoryText : EvidenceRole
  sameObjectProjectEvidence : EvidenceRole
  regionalMechanismScience : EvidenceRole
  generalMechanismScience : EvidenceRole
  currentIndependentLocalExpertEvidence : EvidenceRole
  executionEvidence : EvidenceRole
  historicalClearingEvidence : EvidenceRole

data PaymentState : Set where
  paid : PaymentState
  partiallyPaid : PaymentState
  open : PaymentState
  conditional : PaymentState

record PromotionGate : Set where
  constructor promotion-gate
  field
    consumer : LegalConsumer
    state : PaymentState
    whatScienceNowPays : String
    sameObjectEvidenceAlreadyHeld : String
    firstUnpaidJoin : String
    sourceDependencyRule : String
    noPromotionBoundary : String

open PromotionGate public

s102ThreateningProcessGate : PromotionGate
s102ThreateningProcessGate = promotion-gate
  s102ThreateningProcess
  partiallyPaid
  "Current official guidance and peer-reviewed science support the biological mechanisms by which clearing, fragmentation, reduced functional connectivity, road exposure and population subdivision can affect koalas."
  "9281/2024/OW and A12705838 identify a concrete approved vegetation-clearing/earthworks process; SHG's same-project ecology identifies Koala habitat, connectivity, direct/indirect habitat loss and fragmentation pathways."
  "A current independent ecological opinion should apply the actual s 12/s 102 statutory language to the exact approved process and current Springview/Woogaroo ecological state."
  "Brunton 2026, Frère et al. 2023, McLennan et al. 2025, Dexter et al. 2024 and McLean et al. 2025 are independent literature carriers, but they are not independent observations of Springview. Multiple mechanism papers increase scientific support for a causal pathway; they do not manufacture local exposure/effect facts."
  "General or regional koala science does not itself establish that 9281 is a threatening process in the statutory application."

s102EffectGate : PromotionGate
s102EffectGate = promotion-gate
  s102LikelySignificantDetrimentalEffect
  open
  "The science now provides a strong state-of-the-art framework for evaluating magnitude, connectivity loss, fragmentation, induced movement risk, population subdivision, mitigation effectiveness and survey uncertainty."
  "The proponent's own material records about 136 ha direct habitat clearing, about 26 ha indirect impact, habitat score 7, >500 ha connectivity and a significant-impact conclusion under the older federal framework."
  "Obtain a current independent local expert opinion answering likelihood, magnitude, duration, reversibility, cumulative fragmentation, current habitat/population context and whether the approval's mitigation materially changes the likely effect."
  "The SHG propositions share one proponent-side ecology lineage and must not be counted as several independent ecological producers. The independent literature is method/mechanism evidence, not same-object corroboration."
  "Federal significant-impact terminology, literature on other populations, or perfect map overlap does not equal the Queensland Ministerial opinion of likely significant detrimental effect."

s13PopulationGate : PromotionGate
s13PopulationGate = promotion-gate
  s13ViablePopulationIdentity
  open
  "Current science supports defining koala populations in landscape/metapopulation and genetic-connectivity terms, and warns against equating survey non-detection, project boundaries or static maps with population identity."
  "Springview project evidence establishes habitat function, occurrence evidence and landscape connectivity but does not identify the relevant viable population/community."
  "Independently identify the biologically relevant local/regional Koala population using compatible current occurrence, movement, population/genetic, habitat and landscape evidence rather than the development boundary."
  "McLennan et al. 2025 provides regional genomic context, including coastal southeast Queensland, but does not identify a Springview genomic population. National monitoring also does not identify the local population."
  "Regional genomic vulnerability or an endangered listing does not pay the local viable-population identity required by the s 13 analysis."

s13EssentialityGate : PromotionGate
s13EssentialityGate = promotion-gate
  s13Essentiality
  open
  "Brunton 2026 supports functional-connectivity validation rather than map-only reasoning; Frère et al. 2023 supports realised gene-flow/mitigation testing; current Commonwealth habitat guidance treats movement ground, corridors and metapopulation processes as habitat attributes."
  "Same-project evidence records Woogaroo/Opossum connectivity, >500 ha connected habitat, food trees/scats, habitat score 7 and expected future fragmentation; adverse SHG recovery-value-0/non-viability reasoning is retained."
  "After identifying the relevant viable population/community, evaluate the without-site counterfactual: whether removal or functional severance materially impairs persistence, dispersal/gene flow, breeding/resource access or resilience, and whether alternative habitat is actually substitutable now."
  "The science sources are independent of SHG but mostly general/regional. Their role is to define/test the counterfactual, not to answer the Springview counterfactual without local data."
  "A corridor map, occupied habitat, high habitat score, federal critical-habitat label or general connectivity literature does not itself prove NCA s 13 essentiality."

s43BConditionalGate : PromotionGate
s43BConditionalGate = promotion-gate
  s43BApplicability
  conditional
  "No koala mechanism literature is needed to establish whether s 43B is actually invoked. Historical-clearing and land-use evidence are the relevant evidence class."
  "The current statutory 15-year clearing-history carve-out is source-paid; historical imagery/maturity evidence may later help reconstruct clearing history."
  "First locate an actual proponent/agency reliance on s 43B for an exact clearing action. If located, reconstruct the exact action polygon, pre-EPBC use, 15-year clearing history, forestry status and any specific environmental authorisation."
  "Historical aerials may be independent physical-history evidence, but mature canopy and repeated uncleared appearance are not themselves the legal conclusion that s 43B applies or fails."
  "Do not let an interesting s 43B theory compete with the live s 102/s 13 case unless an actual reliance record makes the exemption a real consumer."

------------------------------------------------------------------------
-- Current legal-machine state.
------------------------------------------------------------------------

record CurrentPromotionState : Set where
  constructor current-promotion-state
  field
    sotaMechanismSnowballPaid : Bool
    sourceAttributionPaid : Bool
    sourceIndependenceAccounted : Bool
    s102LocalExpertBridgePaid : Bool
    s13PopulationIdentityPaid : Bool
    s13EssentialityCounterfactualPaid : Bool
    s43BActualRelianceLocated : Bool
    moreGeneralLiteratureIsFirstPriority : Bool

currentPromotionState : CurrentPromotionState
currentPromotionState = current-promotion-state
  true true true
  false false false false false

------------------------------------------------------------------------
-- Reuse current owners; no second status ontology.
------------------------------------------------------------------------

s102Case : S102.S102CaseState
s102Case = S102.currentS102CaseState

s13Case : S13.S13StressTest
s13Case = S13.currentS13StressTest

s43BCase : S43B.CurrentS43BConclusion
s43BCase = S43B.currentS43BConclusion

s102Dependency : Dependency.ConsumerDependencyState
s102Dependency = Dependency.s102DependencyState

s13Dependency : Dependency.ConsumerDependencyState
s13Dependency = Dependency.s13DependencyState

provenanceBoundary : Provenance.ProvenanceDagBoundary
provenanceBoundary = Provenance.canonicalProvenanceDagBoundary

scienceState : Science.ConsumerScienceState
scienceState = Science.currentConsumerScienceState

------------------------------------------------------------------------
-- WrongType / no-promotion firewalls.
------------------------------------------------------------------------

data PeerReviewedScienceEqualsLocalFact : Set where
data SeveralIndependentPapersEqualSeveralLocalObservations : Set where
data RegionalSEQScienceEqualsSpringviewPopulation : Set where
data GeneralMechanismEqualsStatutoryLikelihood : Set where
data MapConnectivityEqualsFunctionalConnectivity : Set where
data MitigationPlanEqualsMitigationEffectiveness : Set where
data ScienceConsensusEqualsMinisterialOpinion : Set where

peerReviewDoesNotCreateLocalFact : PeerReviewedScienceEqualsLocalFact → ⊥
peerReviewDoesNotCreateLocalFact ()

papersDoNotCreateLocalObservationMultiplicity : SeveralIndependentPapersEqualSeveralLocalObservations → ⊥
papersDoNotCreateLocalObservationMultiplicity ()

regionalScienceDoesNotIdentifySpringviewPopulation : RegionalSEQScienceEqualsSpringviewPopulation → ⊥
regionalScienceDoesNotIdentifySpringviewPopulation ()

generalMechanismDoesNotPayStatutoryLikelihood : GeneralMechanismEqualsStatutoryLikelihood → ⊥
generalMechanismDoesNotPayStatutoryLikelihood ()

mapDoesNotPayFunctionalConnectivity : MapConnectivityEqualsFunctionalConnectivity → ⊥
mapDoesNotPayFunctionalConnectivity ()

mitigationPlanDoesNotProveEffectiveness : MitigationPlanEqualsMitigationEffectiveness → ⊥
mitigationPlanDoesNotProveEffectiveness ()

scienceConsensusDoesNotCreateMinisterialOpinion : ScienceConsensusEqualsMinisterialOpinion → ⊥
scienceConsensusDoesNotCreateMinisterialOpinion ()
