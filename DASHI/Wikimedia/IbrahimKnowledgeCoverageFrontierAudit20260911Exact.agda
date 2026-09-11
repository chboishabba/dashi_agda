module DASHI.Wikimedia.IbrahimKnowledgeCoverageFrontierAudit20260911Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapExact as Roadmap
import DASHI.Wikimedia.IbrahimSnowballStateAnthropologyArchaeologyExact as StateAnthroArch
import DASHI.Wikimedia.IbrahimSnowballLinguisticsSubfieldsAttributionExact as Linguistics
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as EvidenceConsensus

------------------------------------------------------------------------
-- CURRENT FRONTIER AUDIT, 2026-09-11
--
-- This is not a replacement roadmap.  It asks which old roadmap leaves have
-- subsequently been paid by Snowball/BIDI work and records only the surviving
-- debt.  QID, Dewey, DOI/source role and formal coverage remain independent.
------------------------------------------------------------------------

data FrontierStatus : Set where
  paid : FrontierStatus
  partial : FrontierStatus
  open : FrontierStatus
  consumerDriven : FrontierStatus

record FrontierLeaf : Set where
  constructor frontier-leaf
  field
    oldRank : Nat
    surface : String
    status : FrontierStatus
    currentOwners : String
    survivingResidual : String
    exactNextMove : String
open FrontierLeaf public

placeCommunityKnowledgeAuthority : FrontierLeaf
placeCommunityKnowledgeAuthority = frontier-leaf
  1
  "Place/Country <-> Community <-> Knowledge <-> Authority <-> Society/State"
  paid
  "IbrahimCountryCommunityKnowledgeAuthorityBridgeExact; IbrahimBrownInstitutionalEpistemicsCrossPollinationExact; Mabo/Two-Eyed/Snowball authority owners"
  "no generic parent-consolidation debt asserted here; concrete consumers may still discover new axes"
  "continue only from a concrete consumer/residual, not by inventing a broader parent"

scienceKnowledgePlurality : FrontierLeaf
scienceKnowledgePlurality = frontier-leaf
  2
  "Science <-> Knowledge plurality"
  paid
  "IbrahimScienceKnowledgePluralityBridgeExact; skepticism/expertise/trust; verification; evidence/observation/inference; replication/consensus BIDI"
  "truth, expertise, trust, replication independence and consensus remain consumer-indexed"
  "snowball from concrete science/knowledge disputes rather than adding another epistemology owner"

communitySocietySocialScience : FrontierLeaf
communitySocietySocialScience = frontier-leaf
  3
  "Community <-> Society <-> Social science"
  paid
  "IbrahimSnowballCommunitySocietySocialScienceExact; childhood/social psychology; social influence/consent/coercion; manosphere/media lanes"
  "scope, observer, affected voice, consent and provenance remain live axes"
  "continue from concrete population/method/source mismatches"

statePoliticsLawAuthority : FrontierLeaf
statePoliticsLawAuthority = frontier-leaf
  4
  "State <-> Politics <-> Law/Governance <-> Authority"
  paid
  "IbrahimSnowballStateAnthropologyArchaeologyExact; SensibLaw evidence/causation; Mabo/Country; AI/state/security lanes"
  "legal power, legitimacy, causation, scope and non-state authority stay distinct"
  "continue only where a concrete legal/political consumer exposes an unpaid distinction"

archaeologyDiscipline : FrontierLeaf
archaeologyDiscipline = frontier-leaf
  5
  "Archaeology"
  partial
  "IbrahimSnowballStateAnthropologyArchaeologyExact; archive/historiography/causality BIDI; source-acquisition geometry"
  "discipline breadth beyond context/provenance is still incomplete: excavation/field method, chronology/dating, heritage/repatriation and geoarchaeology are not one paid owner"
  "compose existing context/provenance with one concrete archaeological case before adding breadth"

ethnographyMethod : FrontierLeaf
ethnographyMethod = frontier-leaf
  6
  "Ethnography / participant observation"
  open
  "anthropology authority boundary, Two-Eyed/source provenance, testimony/memory, social-influence and archive owners supply substrate"
  "no canonical fieldwork receipt yet binds observer participation, duration, consent/authority, fieldnotes, reflexive position, interpretation and community/source provenance"
  "add one source-bounded ethnography/participant-observation method owner and reuse existing authority/provenance fibres"

linguisticAnthropology : FrontierLeaf
linguisticAnthropology = frontier-leaf
  7
  "Linguistic anthropology"
  partial
  "LinguisticAnthropologyTlureyPragmaticsBridgeExact; IbrahimSnowballLinguisticsSubfieldsAttributionExact"
  "strong situated-pragmatics substrate exists, but repo-wide linguistic-anthropology discipline consolidation remains incomplete"
  "quotient the existing Tlurey/Hymes/Duranti bridge against sociolinguistics and community/authority before adding anything"

geologyBreadth : FrontierLeaf
geologyBreadth = frontier-leaf
  8
  "Geology breadth"
  consumerDriven
  "existing geology/environment/geochemistry/deep-time owners plus agriculture/LES/climate snowballs"
  "no evidence that breadth itself should be filled abstractly; stratigraphy/petrology/tectonics/etc should appear when downstream consumers demand them"
  "do not expand by checklist; wait for concrete residual"

healthcareBreadth : FrontierLeaf
healthcareBreadth = frontier-leaf
  9
  "Health care breadth"
  consumerDriven
  "healthcare access/equality/governance owners and evidence/source architecture"
  "clinical efficacy/public-health/health-services remain separate from governance and should be added only under concrete evidence consumers"
  "consumer-first expansion only"

petrochemistryParent : FrontierLeaf
petrochemistryParent = frontier-leaf
  10
  "Petrochemistry <-> chemistry <-> fossil-fuel/deep-time carbon"
  partial
  "industrial chemistry, petroleum/logistics, deep-time carbon, climate/fossil-fuel owners"
  "shared parent representation is still useful but lower priority than ethnography/method and live consumer residuals"
  "compose only when a chemistry/materials/climate consumer needs the shared carrier"

------------------------------------------------------------------------
-- The first genuinely open method leaf now has exact external identities.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim coverage frontier audit 2026-09-11"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create method validity, field authority, consent or interpretation")

ethnographyQid : Identity.ExternalIdentityDemand
ethnographyQid = mkQid "ethnography" "Q132151"

linguisticAnthropologyQid : Identity.ExternalIdentityDemand
linguisticAnthropologyQid = mkQid "linguistic anthropology" "Q772835"

hammersleyEthnographySource : Attribution.AttributedSource
hammersleyEthnographySource = Attribution.mkDOISource
  "Martyn Hammersley"
  "Ethnography: problems and prospects"
  "Ethnography and Education 1(1), 3-14"
  "2006"
  "10.1080/17457820500512697"
  "https://doi.org/10.1080/17457820500512697"
  Attribution.academicArticleSource
  "methodological discussion of ethnographic boundary, context, interview, representation and commitment problems; does not create community authority or universal method validity"
  Attribution.publicAttribution

shahParticipantObservationSource : Attribution.AttributedSource
shahParticipantObservationSource = Attribution.mkDOISource
  "Alpa Shah"
  "Ethnography? Participant observation, a potentially revolutionary praxis"
  "HAU: Journal of Ethnographic Theory 7(1)"
  "2017"
  "10.14318/hau7.1.008"
  "https://doi.org/10.14318/hau7.1.008"
  Attribution.academicArticleSource
  "source-bounded argument about participant observation as long-duration, relational and reflexive knowledge practice; not proof that every participant-observation design is adequate or authorised"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Frontier order after the audit.
------------------------------------------------------------------------

record CurrentPriority : Set where
  constructor current-priority
  field
    rank : Nat
    residual : String
    whyNow : String
open CurrentPriority public

priority1 : CurrentPriority
priority1 = current-priority 1
  "Ethnography / participant-observation fieldwork receipt"
  "it is the clearest genuinely open Tier-2 method debt and connects anthropology, affected voice, consent, testimony/memory, source provenance and Two-Eyed authority"

priority2 : CurrentPriority
priority2 = current-priority 2
  "Replication/common-source dependence -> consensus provenance graph"
  "the learning-memory-trauma BIDI already proves multiplicity != independence; the remaining gain is to carry explicit source genealogy into consensus/media/OSINT consumers"

priority3 : CurrentPriority
priority3 = current-priority 3
  "Natural-language semantics / sociolinguistics / linguistic-anthropology consolidation"
  "the linguistics snowball reports natural-language semantics and sociolinguistics as the strongest remaining language-family residuals"

priority4 : CurrentPriority
priority4 = current-priority 4
  "Archaeology concrete-case completion"
  "context/provenance is paid but discipline breadth should be driven by a real excavation/dating/heritage consumer rather than checklist inflation"

record FrontierAuditBoundary : Set where
  constructor frontier-audit-boundary
  field
    oldRoadmapRetainedAsHistoricalPriorityObject : Bool
    paidLeavesNotReopenedWithoutConsumer : Bool
    qidDoesNotCreateCoverage : Bool
    doiDoesNotCreateMethodAuthority : Bool
    breadthExpansionConsumerDriven : Bool
    firstOpenMethodLeafIdentified : Bool
    presentFrontierClaimedComplete : Bool
open FrontierAuditBoundary public

canonicalFrontierAuditBoundary : FrontierAuditBoundary
canonicalFrontierAuditBoundary = frontier-audit-boundary
  true true true true true true false

oldRoadmapPolicy : Roadmap.RoadmapPolicy
oldRoadmapPolicy = Roadmap.canonicalRoadmapPolicy

stateAnthropologyArchaeologyBoundary : StateAnthroArch.StateAnthropologyArchaeologySnowballBoundary
stateAnthropologyArchaeologyBoundary = StateAnthroArch.canonicalStateAnthropologyArchaeologySnowballBoundary

linguisticsBoundary : Linguistics.LinguisticsSnowballAttributionBoundary
linguisticsBoundary = Linguistics.canonicalLinguisticsSnowballAttributionBoundary

evidenceConsensusBoundary : EvidenceConsensus.LearningMemoryTraumaReplicationConsensusBoundary
evidenceConsensusBoundary = EvidenceConsensus.canonicalLearningMemoryTraumaReplicationConsensusBoundary
