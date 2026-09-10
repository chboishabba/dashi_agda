module DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapDeltaExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapExact as Base
import DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapBrownExtensionExact as Brown
import DASHI.Wikimedia.IbrahimSnowballCommunitySocietySocialScienceExact as Community
import DASHI.Wikimedia.IbrahimSnowballScienceKnowledgePluralityBridgeExact as Science
import DASHI.Wikimedia.IbrahimSnowballStateAnthropologyArchaeologyExact as Archaeology
import DASHI.Wikimedia.IbrahimSnowballLinguisticsSubfieldsAttributionExact as Linguistics
import DASHI.Wikimedia.IbrahimSnowballArchiveHistoriographyCausalityBidiExact as Archive
import DASHI.Wikimedia.IbrahimSnowballSensibLawEvidenceObservationTestimonyCausationBidiExact as Evidence
import DASHI.Wikimedia.IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact as Testimony
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as Memory
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Identity

------------------------------------------------------------------------
-- ROADMAP DELTA
--
-- The original IbrahimKnowledgeCoverageRoadmapExact remains the historical
-- priority projection. This owner records what later Snowball/BIDI work has
-- paid, narrowed or left genuinely open. It is a status/navigation adapter,
-- not a replacement ontology or planner.
------------------------------------------------------------------------

data CompletionState : Set where
  paid : CompletionState
  substantiallyPaid : CompletionState
  partial : CompletionState
  open : CompletionState

record RoadmapDeltaLeaf : Set where
  constructor roadmap-delta-leaf
  field
    originalRank : Nat
    originalSurface : String
    currentState : CompletionState
    laterOwners : String
    survivingResidual : String
    qidState : String
    deweyState : String
    doiSourceState : String
    nextCompletionTest : String
open RoadmapDeltaLeaf public

placeCommunityKnowledgeAuthorityDelta : RoadmapDeltaLeaf
placeCommunityKnowledgeAuthorityDelta = roadmap-delta-leaf
  1
  "Place/Country <-> Community <-> Knowledge <-> Power/Authority <-> Society/State"
  substantiallyPaid
  "IbrahimCountryCommunityKnowledgeAuthorityBridgeExact; IbrahimSnowballGeographyPlaceTerritoryExact; Mabo/Country/Two-Eyed owners; Brown extension"
  "coverage consolidation remains: prove/document which downstream consumers still require an unrepresented authority/place/provenance coordinate"
  "major parent entities already QID-bound in their local owners"
  "Dewey remains a navigation coordinate, not authority; no forced unique shelf"
  "source-role/provenance owners present; no DOI required for every legal/community source"
  "residual-driven audit finds no downstream consumer that factors through generic place/state while erasing Country/community authority"

scienceKnowledgePluralityDelta : RoadmapDeltaLeaf
scienceKnowledgePluralityDelta = roadmap-delta-leaf
  2
  "Science <-> Knowledge with plural epistemic boundary"
  paid
  "IbrahimScienceKnowledgePluralityBridgeExact; skepticism/expertise/trust; verification; evidence/measurement/inference; replication/consensus"
  "only breadth/consumer-specific additions remain; parent noncollapse is already explicit"
  "science/knowledge-adjacent QIDs are retained in local owners rather than one scalar parent identity"
  "multiple Dewey views may coexist; classification does not define epistemic role"
  "DOI/source attribution is first-class and does not import proof"
  "new work should reuse the parent and add only a concrete unpaid consumer"

communitySocietySocialScienceDelta : RoadmapDeltaLeaf
communitySocietySocialScienceDelta = roadmap-delta-leaf
  3
  "Community <-> Society <-> Social science"
  paid
  "IbrahimSnowballCommunitySocietySocialScienceExact; social psychology/ethics; social influence/consent/coercion; Brown observer/agency bridges"
  "no generic parent debt identified; continue only from concrete scale/observer failures"
  "community/society/social-science identities are locally source/QID bounded"
  "no Dewey location is treated as social-scale semantics"
  "primary empirical and institutional sources retain their own identifiers"
  "future child/community cases must reuse scale/observer nonfactorability rather than create another parent"

statePoliticsLawAuthorityDelta : RoadmapDeltaLeaf
statePoliticsLawAuthorityDelta = roadmap-delta-leaf
  4
  "State <-> Politics <-> Law/Governance <-> Authority"
  substantiallyPaid
  "IbrahimSnowballStateAnthropologyArchaeologyExact; SensibLaw evidence/legal-source/causation owners; Country/Mabo; Brown authority/contestability"
  "remaining debt is mostly jurisdiction- and element-specific, not a missing generic state/law parent"
  "state/politics/law/authority QIDs remain external identity only"
  "legal classification and Dewey classification cannot create jurisdiction/applicability"
  "primary law may correctly have no DOI; legal authority uses jurisdiction/current-validity/source receipts"
  "route new legal questions through typed element/causation/scope consumers"

archaeologyDelta : RoadmapDeltaLeaf
archaeologyDelta = roadmap-delta-leaf
  5
  "Archaeology"
  substantiallyPaid
  "IbrahimSnowballStateAnthropologyArchaeologyExact; ArchiveHistoriographyCausalityBidiExact; source-acquisition/provenance owners"
  "discipline breadth such as excavation/taphonomy/dating/heritage may still require concrete consumer owners"
  "archaeology identity already traversed in Ibrahim anthropology branch"
  "Dewey breadth remains secondary to method/context provenance"
  "archival/historical and method sources can carry DOI or canonical institutional identifiers"
  "only add a new archaeology leaf when a concrete archaeological claim cannot be expressed by context/source/method/history carriers"

ethnographyDelta : RoadmapDeltaLeaf
ethnographyDelta = roadmap-delta-leaf
  6
  "Ethnography / participant observation"
  partial
  "Two-Eyed/community observer machinery; Brown observer plurality; anthropology/divination source-role work; testimony/credibility owners"
  "one canonical fieldwork receipt is still useful: observer relation, participation, consent/authority, time, interpretation, provenance, affected-subject voice"
  "exact ethnography/participant-observation QID audit remains a live acquisition item if not already paid elsewhere"
  "exact Dewey retained unresolved until inspected"
  "method papers/source records should be attached when the fieldwork receipt is specialised"
  "compose one generic ethnography receipt from existing observer/source/consent primitives without duplicating anthropology"

linguisticAnthropologyDelta : RoadmapDeltaLeaf
linguisticAnthropologyDelta = roadmap-delta-leaf
  7
  "Linguistic anthropology"
  substantiallyPaid
  "IbrahimSnowballLinguisticsSubfieldsAttributionExact plus anthropology/community/culture source boundaries"
  "remaining debt is empirical/source breadth, not a missing language ontology"
  "linguistic identities are source/QID bounded in the subfields owner"
  "Dewey classification remains supplemental"
  "language-formalism and empirical linguistic sources retain separate attribution"
  "add only a concrete language-practice/community consumer that survives existing grammar/provenance projections"

geologyBreadthDelta : RoadmapDeltaLeaf
geologyBreadthDelta = roadmap-delta-leaf
  8
  "Geology beyond salt/geochemistry"
  open
  "existing Geology/Environment/DeepTimeCarbon owners plus Ibrahim archaeology/geology joins"
  "stratigraphy, petrology, sedimentology, tectonics, geomorphology, geophysics and deep-time method breadth remain the clearest original roadmap breadth gap"
  "attach exact QIDs opportunistically per demanded subdiscipline"
  "attach Dewey only where explicitly inspected"
  "attach DOI/primary survey or method sources per concrete geological consumer"
  "choose the first downstream consumer that actually needs a missing geological method rather than blanket-filling taxonomy"

healthcareBreadthDelta : RoadmapDeltaLeaf
healthcareBreadthDelta = roadmap-delta-leaf
  9
  "Health care beyond access/equality/governance"
  open
  "HealthcareEqualityInvariant; HealthcareAccessDistortion; governance/access owners"
  "clinical/public-health/health-services breadth remains intentionally unpaid unless a concrete consumer requires it"
  "QID acquisition should distinguish health care, public health, clinical medicine and health services"
  "Dewey/medical classifications must not create efficacy evidence"
  "clinical claims require their own medical evidence/source role; governance sources cannot pay efficacy"
  "expand only from a concrete non-medical-to-medical WrongType residual"

petrochemistryDelta : RoadmapDeltaLeaf
petrochemistryDelta = roadmap-delta-leaf
  10
  "Petrochemistry <-> Chemistry <-> Fossil-fuel/deep-time carbon"
  partial
  "SaltPetroleumIndustrialChemistryNetworkExact; IndustrialChemistryLogisticsEverything; DeepTimeCarbonBiosphereFossilFuelBidiExact; climate/AI-state branches"
  "canonical parent consolidation remains useful if current consumers still duplicate feedstock/refining/materials/emissions links"
  "QIDs should distinguish petroleum, petrochemistry, refining, feedstock and fossil fuel"
  "Dewey is classification only and may have multiple chemistry/engineering views"
  "process-specific DOI/technical sources remain separate from climate/economic attribution"
  "audit for duplicated petroleum->chemistry->materials/emissions edges before adding a parent owner"

------------------------------------------------------------------------
-- New cross-cutting spine created after the original roadmap.
------------------------------------------------------------------------

record EpistemicSpine : Set where
  constructor epistemic-spine
  field
    acquisition : String
    cognition : String
    evidence : String
    independence : String
    socialEpistemics : String
    legalBoundary : String
    identityCoordinates : String
open EpistemicSpine public

currentEpistemicSpine : EpistemicSpine
currentEpistemicSpine = epistemic-spine
  "bibliography -> access -> primary inspection -> transcription -> source criticism"
  "experience/perception -> memory -> retrieval/update -> report/testimony"
  "observation/measurement -> inference -> causal audit"
  "corroboration/replication multiplicity -> provenance independence/common-source audit"
  "expertise/trust/skepticism -> reproducibility -> consensus, without consensus=truth"
  "source authority -> legal element -> factual causation -> scope/liability"
  "QID != Dewey != DOI != source role != truth/proof authority"

------------------------------------------------------------------------
-- Re-ranked next actions. These are residual priorities, not a new ontology.
------------------------------------------------------------------------

record NextPriority : Set where
  constructor next-priority
  field
    rank : Nat
    target : String
    reason : String
    completionTest : String
open NextPriority public

priority1RoadmapConsolidation : NextPriority
priority1RoadmapConsolidation = next-priority
  1
  "Canonical roadmap/current-state consolidation"
  "the original 1-10 roadmap now overstates several debts after extensive Snowball/BIDI payment"
  "one inspectable current-state owner points from old leaves to paid owners and identifies only surviving residuals"

priority2IndependenceConsensus : NextPriority
priority2IndependenceConsensus = next-priority
  2
  "Corroboration / replication / common-source dependence / consensus"
  "same provenance-independence defect now appears in witnesses, papers, media, OSINT, expert reports and AI summaries"
  "a shared provenance-sensitive independence consumer can be reused across those domains without identifying replication with truth"

priority3EthnographyReceipt : NextPriority
priority3EthnographyReceipt = next-priority
  3
  "Ethnography / participant-observation receipt"
  "the observer/community/consent/provenance pieces exist but remain distributed"
  "one thin composition receipt covers observer relation, participation, authority/consent, time, interpretation, source role and affected voice"

priority4GeologyConsumer : NextPriority
priority4GeologyConsumer = next-priority
  4
  "First concrete geology breadth consumer"
  "geology remains the clearest original substantive breadth gap"
  "one downstream demand proves which missing method/subdiscipline is actually needed before taxonomy expansion"

priority5HealthcareConsumer : NextPriority
priority5HealthcareConsumer = next-priority
  5
  "First concrete healthcare breadth consumer"
  "governance/access are represented; clinical/public-health breadth should remain consumer-driven"
  "a real consumer demonstrates a missing clinical/public-health distinction and supplies appropriate evidence authority"

------------------------------------------------------------------------
-- Roadmap policy update.
------------------------------------------------------------------------

record RoadmapDeltaPolicy : Set where
  constructor roadmap-delta-policy
  field
    originalRoadmapPreservedAsHistory : Bool
    paidLeavesNotReopenedByDefault : Bool
    partialLeavesRequireConcreteResidual : Bool
    openBreadthExpandedOnlyByConsumerDemand : Bool
    qidDeweyDoiTravelTogetherWhenRelevant : Bool
    qidDeweyDoiAreInterchangeable : Bool
    sourceIdentityCreatesProof : Bool
    nextWorkIsResidualDriven : Bool
open RoadmapDeltaPolicy public

canonicalRoadmapDeltaPolicy : RoadmapDeltaPolicy
canonicalRoadmapDeltaPolicy = roadmap-delta-policy
  true true true true true false false true

baseRoadmapPolicy : Base.RoadmapPolicy
baseRoadmapPolicy = Base.canonicalRoadmapPolicy

brownRoadmapPolicy : Brown.BrownExtendedRoadmapPolicy
brownRoadmapPolicy = Brown.canonicalBrownExtendedRoadmapPolicy

identityBoundary : Identity.SymbolicVerificationDeweyQidDoiBoundary
identityBoundary = Identity.canonicalSymbolicVerificationDeweyQidDoiBoundary
