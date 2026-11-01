module DASHI.Wikimedia.IbrahimSnowballKnowledgeCultureHistoryFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.KnowledgeContentAuthoritySeparationExact as Knowledge
import DASHI.Core.SnowballPluralLensInvariantExact as Snowball
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.IbrahimSnowballCommunitySocietySocialScienceExact as Prior

------------------------------------------------------------------------
-- NEXT IBRAHIM/SNOWBALL FRONTIER: KNOWLEDGE / CULTURE / HISTORY
--
-- External observations inspected 2026-09-10 are navigation evidence only:
--   * Knowledge distinguishes familiarity/awareness/understanding, propositional
--     knowledge, know-how, acquaintance, individual and collective knowledge;
--   * Culture spans socially transmitted practices, meanings, knowledge,
--     beliefs, law/custom and material expression;
--   * History distinguishes past events, the academic inquiry into the past,
--     and representations/narratives of the past.
--
-- None of those Wikipedia descriptions creates DASHI authority.  They nominate
-- exactly the kinds of semantic-scale/source/observer distinctions that the
-- snowball invariant must test against existing DASHI owners.
------------------------------------------------------------------------

ibrahimSource : Attribution.AttributedSource
ibrahimSource = Attribution.mkDOISource
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network"
  "Journal of Computational Science 19, 21-30"
  "2017"
  "10.1016/j.jocs.2016.12.001"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  Attribution.academicArticleSource
  "external graph-navigation prior only"
  Attribution.publicAttribution

data FrontierNode : Set where
  knowledgeNode cultureNode historyNode : FrontierNode

record SnowballNodeAudit : Set where
  constructor snowball-node-audit
  field
    node : FrontierNode
    currentExternalRole : String
    existingDashiOwner : String
    principalNoncollapse : String
    sourceAttributionRequired : Bool
    twoEyedPluralComparisonRequired : Bool
    semanticScaleIndexed : Bool
    currentNodeDescriptionDefinesDashiOntology : Bool
    presentAxisVocabularyClaimedComplete : Bool
open SnowballNodeAudit public

knowledgeAudit : SnowballNodeAudit
knowledgeAudit = snowball-node-audit
  knowledgeNode
  "broad external knowledge concept; current EN includes propositional, practical, acquaintance, individual, collective and documented knowledge"
  "DASHI.Core.KnowledgeContentAuthoritySeparationExact; plural-knowledge and science/knowledge Wikimedia bridges"
  "content != practice != situated authority; scientific/documented knowledge does not exhaust community/Indigenous/affected-subject knowledge"
  true true true false false

cultureAudit : SnowballNodeAudit
cultureAudit = snowball-node-audit
  cultureNode
  "external connective concept spanning practices, meanings, knowledge, beliefs, law/custom, symbols and material expression"
  "DASHI.Culture.Everything; Indigenous, Kimmerer, feminist, dialectical, Wittgenstein/use, historical-totality and cultural-provenance owners"
  "shared cultural label does not erase provenance, grammar, community authority, place, history or internal disagreement"
  true true true false false

historyAudit : SnowballNodeAudit
historyAudit = snowball-node-audit
  historyNode
  "external concept distinguishes past event, historical inquiry and representation/narrative of the past"
  "DASHI.Culture.HistoricalSocialTotalityBidiExact; PhilosophyClaimProvenanceHistoryBidiExact; source/provenance and deep-time owners"
  "event != evidence != source != historical representation != present interpretation"
  true true true false false

------------------------------------------------------------------------
-- Knowledge regression: a shared content surface cannot recover situated
-- authority. This mirrors the existing KnowledgeContentAuthoritySeparation owner
-- without replacing it.
------------------------------------------------------------------------

data KnowledgeState : Set where
  sameContentNoSituatedAuthority : KnowledgeState
  sameContentWithSituatedAuthority : KnowledgeState

data ContentSurface : Set where sameContent : ContentSurface
data AuthorityAnswer : Set where noAuthority yesAuthority : AuthorityAnswer

contentProjection : KnowledgeState → ContentSurface
contentProjection state = sameContent

situatedAuthorityAnswer : KnowledgeState → AuthorityAnswer
situatedAuthorityAnswer sameContentNoSituatedAuthority = noAuthority
situatedAuthorityAnswer sameContentWithSituatedAuthority = yesAuthority

contentAuthorityDefect :
  INF.NonFactorabilityWitness contentProjection situatedAuthorityAnswer
contentAuthorityDefect = INF.nonFactorabilityWitness
  sameContentNoSituatedAuthority
  sameContentWithSituatedAuthority
  refl
  (λ ())

contentCannotFactorSituatedAuthority :
  INF.FactorsThrough contentProjection situatedAuthorityAnswer → ⊥
contentCannotFactorSituatedAuthority =
  INF.witnessRulesOutEveryFlatFactorisation contentAuthorityDefect

------------------------------------------------------------------------
-- History regression: the same event identifier may support distinct
-- source-bounded representations. An event-only projection therefore cannot
-- answer every interpretation/provenance query.
------------------------------------------------------------------------

data HistoryState : Set where
  sameEventRepresentationA : HistoryState
  sameEventRepresentationB : HistoryState

data EventSurface : Set where sameEvent : EventSurface
data RepresentationAnswer : Set where representationA representationB : RepresentationAnswer

eventProjection : HistoryState → EventSurface
eventProjection state = sameEvent

representationAnswer : HistoryState → RepresentationAnswer
representationAnswer sameEventRepresentationA = representationA
representationAnswer sameEventRepresentationB = representationB

eventRepresentationDefect :
  INF.NonFactorabilityWitness eventProjection representationAnswer
eventRepresentationDefect = INF.nonFactorabilityWitness
  sameEventRepresentationA
  sameEventRepresentationB
  refl
  (λ ())

eventCannotFactorEveryHistoricalRepresentation :
  INF.FactorsThrough eventProjection representationAnswer → ⊥
eventCannotFactorEveryHistoricalRepresentation =
  INF.witnessRulesOutEveryFlatFactorisation eventRepresentationDefect

------------------------------------------------------------------------
-- Snowball interpretation. These finite regressions discover axes but do not
-- define the universal axis vocabulary.  A later consumer may add new source,
-- place, authority, chronology, grammar, material, observer or method axes and
-- must preserve all previously relevant ones.
------------------------------------------------------------------------

record FrontierSnowballBoundary : Set where
  constructor frontier-snowball-boundary
  field
    priorCommunitySocietyTraversalReused : Bool
    knowledgeContentAuthoritySeparationReused : Bool
    cultureRichNotMissingLeaf : Bool
    historyRichNotMissingLeaf : Bool
    failedFactorisationCanDemandNewAxis : Bool
    attributionRoleRetainedThroughTraversal : Bool
    twoEyedCoordinationDoesNotRequireSynthesis : Bool
    nextFrontierIncludesStatePolity : Bool
    nextFrontierIncludesAnthropologyArchaeology : Bool
    currentFiniteAxisSetIsUniversal : Bool
open FrontierSnowballBoundary public

canonicalFrontierSnowballBoundary : FrontierSnowballBoundary
canonicalFrontierSnowballBoundary = frontier-snowball-boundary
  true true true true true true true true true false

------------------------------------------------------------------------
-- Existing owner receipts / firewalls.
------------------------------------------------------------------------

knowledgeAuthorityBoundary : Knowledge.KnowledgeAuthorityBoundary
knowledgeAuthorityBoundary = Knowledge.canonicalKnowledgeAuthorityBoundary

data WikipediaKnowledgeCreatesCommunityAuthority : Set where
data SharedCultureImpliesSharedGrammar : Set where
data HistoricalNarrativeEqualsPastEvent : Set where
data FirstLinkEdgePaysSemanticParent : Set where

wikipediaKnowledgeDoesNotCreateCommunityAuthority :
  WikipediaKnowledgeCreatesCommunityAuthority → ⊥
wikipediaKnowledgeDoesNotCreateCommunityAuthority ()

sharedCultureDoesNotForceSharedGrammar : SharedCultureImpliesSharedGrammar → ⊥
sharedCultureDoesNotForceSharedGrammar ()

historicalNarrativeDoesNotEqualPastEvent : HistoricalNarrativeEqualsPastEvent → ⊥
historicalNarrativeDoesNotEqualPastEvent ()

firstLinkDoesNotPaySemanticParent : FirstLinkEdgePaysSemanticParent → ⊥
firstLinkDoesNotPaySemanticParent ()

priorTraversalBoundary : Prior.SocialFunnelSnowballPayment
priorTraversalBoundary = Prior.currentSocialFunnelPayment
