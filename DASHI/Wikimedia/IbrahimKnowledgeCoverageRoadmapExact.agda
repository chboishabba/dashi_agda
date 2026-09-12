module DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimEnglishPluralKnowledgeFunnelBridgeExact as Plural
import DASHI.Wikimedia.IbrahimEnglishArchaeologyGeologyPetrochemGapExact as Cross
import DASHI.Wikimedia.IbrahimEnglishCommunityStateScienceParentBridgeExact as Parent
import DASHI.Wikimedia.IbrahimEnglishSocialScienceFunnelBridgeExact as Social

------------------------------------------------------------------------
-- IBRAHIM-GUIDED KNOWLEDGE COVERAGE ROADMAP
--
-- The roadmap is a dependency/priority projection over already-existing DASHI
-- owners. It is not a second ontology or project planner.
--
-- Lessons retained from the previous tranches:
--
-- 1. Wikipedia first-link flow is a navigation prior, not semantic authority.
-- 2. Raw first link and selected DASHI conceptual parent are distinct objects.
-- 3. A low Dewey/module count is not evidence of absent knowledge.
-- 4. Existing rich traditions must be quotiented before any new owner is made.
-- 5. Cross-pollination may preserve disagreement/non-factorability rather than
--    producing one synthesis.
-- 6. QID = external identity coordinate only; source/proof/authority stay
--    separate.
-- 7. Country/community/custodial authority cannot be reconstructed from a
--    generic scientific or governmental observer.
------------------------------------------------------------------------

data RoadmapDebtClass : Set where
  parentConsolidation : RoadmapDebtClass
  genuineDisciplineGap : RoadmapDebtClass
  breadthExpansion : RoadmapDebtClass
  pluralKnowledgeBridge : RoadmapDebtClass
  sourceOrMethodDebt : RoadmapDebtClass

record RoadmapLeaf : Set where
  constructor roadmap-leaf
  field
    rank : Nat
    debtClass : RoadmapDebtClass
    surface : String
    existingSubstrate : String
    survivingDebt : String
    completionTest : String
    wikipediaCanPay : Bool
open RoadmapLeaf public

------------------------------------------------------------------------
-- Tier 1: highest-flow parent joints. These pay many existing leaves at once.
------------------------------------------------------------------------

placeCommunityKnowledgeAuthority : RoadmapLeaf
placeCommunityKnowledgeAuthority = roadmap-leaf
  1 pluralKnowledgeBridge
  "Place/Country <-> Community <-> Knowledge <-> Power/Authority <-> Society/State"
  "IndigenousKnowledgeStoryTwoEyedSeeingBidiExact; KimmererTwoEyedSeeingInterpretationBoundaryExact; KimmererBraidingAcknowledgement; IntersectionalNonFactorability; Mabo/Country/SensibLaw/Governance; SituatedFormalisationBoundaryExact"
  "one typed bridge retaining place, custodianship, community, knowledge role, observer, authority, provenance and state/society coordinates without collapsing any pair"
  "all projections are explicit; no generic observer or state credential can manufacture community/Country authority; each knowledge lane retains its source boundary"
  false

scienceKnowledgePlurality : RoadmapLeaf
scienceKnowledgePlurality = roadmap-leaf
  2 parentConsolidation
  "Science <-> Knowledge with plural epistemic boundary"
  "Physics/Biology/Chemistry/Geology/Reasoning science owners; MultiObserverScienceQuotient; OpenScienceKnowledgeRelease; Two-Eyed Seeing; Haraway situated formalisation"
  "repo-wide Science/Knowledge parent that distinguishes empirical, formal, situated, Indigenous/community and source-provenance roles"
  "Science parent exists without identifying science with all knowledge or downgrading non-scientific knowledge to absence"
  false

communitySocietySocialScience : RoadmapLeaf
communitySocietySocialScience = roadmap-leaf
  3 parentConsolidation
  "Community <-> Society <-> Social science"
  "CommunityConnectednessTopology; CulturalMembershipBoundary; SocialScience funnel; psychology/economics/sociology/culture owners"
  "canonical bridge from situated communities to society-level observation and social-science inquiry, preserving scale and observer changes"
  "community fact cannot silently become society-wide fact; social-science observation records scope/source/method"
  false

statePoliticsLawAuthority : RoadmapLeaf
statePoliticsLawAuthority = roadmap-leaf
  4 parentConsolidation
  "State <-> Politics <-> Law/Governance <-> Authority"
  "Governance/*; SensibLaw; Mabo/sovereignty/Country; PoliticalSciencePolitics bridge"
  "canonical state/political-entity parent with government, territory, population, legitimacy, sovereignty and non-state authority kept separable"
  "state != government != nation != society; legal power != legitimacy; state authority does not erase Country/community authority"
  false

------------------------------------------------------------------------
-- Tier 2: genuine discipline/method gaps after quotient against existing repo.
------------------------------------------------------------------------

archaeologyDiscipline : RoadmapLeaf
archaeologyDiscipline = roadmap-leaf
  5 genuineDisciplineGap
  "Archaeology"
  "Anthropology/Humanity bridge; Geology; Culture; provenance; rights/heritage; physics/chemistry dating substrate"
  "discipline owner spanning material culture, context/excavation, chronology, human-past inference, heritage/repatriation and geoarchaeology"
  "archaeological claims require method/context/source receipts and cannot be paid by repository-'archaeology' terminology"
  false

ethnographyMethod : RoadmapLeaf
ethnographyMethod = roadmap-leaf
  6 sourceOrMethodDebt
  "Ethnography / participant observation"
  "observer/provenance machinery; Anthropology bridge; community/Country source boundaries"
  "fieldwork receipt with observer relation, community, time, method, consent/authority, interpretation and provenance"
  "generic observer records are insufficient; community participation and authority are explicit"
  false

linguisticAnthropology : RoadmapLeaf
linguisticAnthropology = roadmap-leaf
  7 genuineDisciplineGap
  "Linguistic anthropology"
  "language/grammar/reasoning carriers; Anthropology/Humanity bridge; culture and community owners"
  "discipline/source bridge connecting language practice to culture/community without reducing language to syntax"
  "language-formalism reuse is explicit but cannot substitute for empirical linguistic-anthropology evidence"
  false

------------------------------------------------------------------------
-- Tier 3: breadth gaps in real existing domains.
------------------------------------------------------------------------

geologyBreadth : RoadmapLeaf
geologyBreadth = roadmap-leaf
  8 breadthExpansion
  "Geology beyond salt/geochemistry"
  "DASHI/Geology/Everything; environment/geochemistry/industrial joins"
  "stratigraphy, petrology, sedimentology, tectonics, geomorphology, geophysics and deep-time bridges as demanded by downstream consumers"
  "new leaves reuse the Geology owner and carry method/source receipts; no parallel geology namespace"
  false

healthcareBreadth : RoadmapLeaf
healthcareBreadth = roadmap-leaf
  9 breadthExpansion
  "Health care beyond access/equality/governance"
  "HealthcareEqualityInvariant; HealthcareAccessDistortion; delegated essential-service and clinical institutional owners"
  "clinical/public-health/health-services breadth only where a concrete consumer requires it"
  "governance/access claims remain distinct from clinical efficacy or medical evidence"
  false

petrochemistryParent : RoadmapLeaf
petrochemistryParent = roadmap-leaf
  10 parentConsolidation
  "Petrochemistry <-> Chemistry <-> Fossil-fuel/deep-time carbon"
  "SaltPetroleumIndustrialChemistryNetworkExact; IndustrialChemistryLogisticsEverything; DeepTimeCarbonBiosphereFossilFuelBidiExact; Geology"
  "canonical parent bridge from geological carbon/feedstock through refining/petrochemistry to materials/manufacture, energy and emissions"
  "process-specific chemistry remains distinct; fossil-fuel history, chemistry, economics and climate consequences are separately sourced"
  false

------------------------------------------------------------------------
-- Philosophical/critical lanes are not backlog leaves. They are active
-- operators on the roadmap and must survive cross-domain projection.
------------------------------------------------------------------------

data RoadmapOperator : Set where
  twoEyedPlurality : RoadmapOperator
  braidedReciprocity : RoadmapOperator
  intersectionalNonFactorability : RoadmapOperator
  situatedFeministKnowledge : RoadmapOperator
  dialecticalRevision : RoadmapOperator
  psychoanalyticCriticalGrammar : RoadmapOperator
  antiLacanianFeministDifference : RoadmapOperator

record OperatorRole : Set where
  constructor operator-role
  field
    operator : RoadmapOperator
    existingOwner : String
    role : String
    forbiddenCollapse : String
open OperatorRole public

twoEyedRole : OperatorRole
twoEyedRole = operator-role twoEyedPlurality
  "KimmererTwoEyedSeeingInterpretationBoundaryExact / IndigenousKnowledgeTwoEyedValidation"
  "coordinate different knowledge systems without requiring reduction to one master observer"
  "plural knowledge -> one universal epistemology"

braidedRole : OperatorRole
braidedRole = operator-role braidedReciprocity
  "KimmererBraidingAcknowledgement / CulturalProvenanceBoundaryCore"
  "retain relation, reciprocity, place, community and obligation in knowledge projection"
  "acknowledgement/source inspiration -> universal Indigenous authority"

intersectionalRole : OperatorRole
intersectionalRole = operator-role intersectionalNonFactorability
  "DASHI/Core/IntersectionalNonFactorability"
  "detect projections that lose interacting situated coordinates"
  "intersectionality -> independent identity checklist"

situatedRole : OperatorRole
situatedRole = operator-role situatedFeministKnowledge
  "SituatedFormalisationBoundaryExact; Butler/Plumwood/Trinh/Scott/Irigaray source owners"
  "retain observer position, power, category construction and difference without hierarchy"
  "feminism -> one canonical school or identity coordinate"

dialecticalRole : OperatorRole
dialecticalRole = operator-role dialecticalRevision
  "HegelDialecticPrimarySourceBoundaryExact + DialecticalMaterialRevisionExact + Zizek lanes"
  "reopen contradictions/residuals and distinguish source genealogy from DASHI reusable revision"
  "Hegel/Marx/Zizek attribution -> DASHI generic operator identity"

psychoanalyticRole : OperatorRole
psychoanalyticRole = operator-role psychoanalyticCriticalGrammar
  "LacanSignifierSubjectCore; LacanDiscourseMatheme; LacanZizekIdeologyBridge"
  "inspect subject/signifier/discourse/ideology projections where relevant"
  "formal psychoanalytic carrier -> empirical clinical authority"

antiLacanianRole : OperatorRole
antiLacanianRole = operator-role antiLacanianFeministDifference
  "LacanIrigarayTernaryGrammarBridgeExact; CriticalRelationalGrammarSourceRegistryExact"
  "permit shared carrier with incompatible grammar; preserve feminist critique rather than force synthesis"
  "Lacan carrier -> Irigaray grammar"

------------------------------------------------------------------------
-- Priority rule: high-flow joins first, missing disciplines second, breadth
-- only after shared parents stop hiding the true residual.
------------------------------------------------------------------------

record RoadmapPolicy : Set where
  constructor roadmap-policy
  field
    quotientExistingRepoFirst : Bool
    highFlowParentBeforeLeafInflation : Bool
    rawFirstLinkIsNavigationOnly : Bool
    pluralKnowledgeMayRemainNonEquivalent : Bool
    authorityAndProvenanceAreFirstClass : Bool
    missingDeweyCountMeansMissingKnowledge : Bool
    wikipediaCanPayFormalCoverage : Bool
open RoadmapPolicy public

canonicalRoadmapPolicy : RoadmapPolicy
canonicalRoadmapPolicy = roadmap-policy
  true true true true true false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SharedFunnelCreatesEpistemicEquivalence : Set where
data StateAuthorityCreatesCountryAuthority : Set where
data ScienceContainsAllKnowledge : Set where
data PhilosophicalOperatorPaysEmpiricalDiscipline : Set where
data CrossPollinationRequiresSynthesis : Set where

sharedFunnelDoesNotCreateEquivalence : SharedFunnelCreatesEpistemicEquivalence → ⊥
sharedFunnelDoesNotCreateEquivalence ()
stateDoesNotCreateCountryAuthority : StateAuthorityCreatesCountryAuthority → ⊥
stateDoesNotCreateCountryAuthority ()
scienceDoesNotContainAllKnowledge : ScienceContainsAllKnowledge → ⊥
scienceDoesNotContainAllKnowledge ()
philosophyDoesNotPayEmpiricalDiscipline : PhilosophicalOperatorPaysEmpiricalDiscipline → ⊥
philosophyDoesNotPayEmpiricalDiscipline ()
crossPollinationNeedNotSynthesize : CrossPollinationRequiresSynthesis → ⊥
crossPollinationNeedNotSynthesize ()
