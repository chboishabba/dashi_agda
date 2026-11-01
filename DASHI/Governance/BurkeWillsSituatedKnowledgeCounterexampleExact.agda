module DASHI.Governance.BurkeWillsSituatedKnowledgeCounterexampleExact where

------------------------------------------------------------------------
-- BURKE & WILLS / SITUATED KNOWLEDGE COUNTEREXAMPLE
--
-- This is deliberately not a theorem that colonial expeditions never used
-- Indigenous knowledge.  The historical record shows both dependence on
-- Indigenous guides/knowledge and failures to use or retain that knowledge.
--
-- Sources / bounded roles:
--
-- State Library Victoria, "Burke, Wills & Aboriginal guides" (Ergo).
-- Institution: State Library Victoria. No DOI asserted.
-- Source role: Dick's assistance, Yandruwandha support, Burke's documented
-- contempt/suspicion, and the expedition's failure to carry an Indigenous guide
-- on the final Cooper Creek to Gulf leg.
--
-- National Museum of Australia, "Burke and Wills", updated 24 Oct 2025.
-- Institution: National Museum of Australia. No DOI asserted.
-- Source role: Yandruwandha assistance, King survival, nardoo preparation and
-- later pastoral-expansion consequences.
--
-- Primary-source anchor cited by SLV:
-- William John Wills, diary/journal, 1861; National Library of Australia
-- manuscript MS 30/7; no DOI asserted.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record KnowledgeStrand : Set where
  constructor knowledgeStrand
  field
    prestigeAuthority : Nat
    placeSpecificCompetence : Nat
    institutionallyRetained : Bool

colonialExpeditionKnowledge : KnowledgeStrand
colonialExpeditionKnowledge = knowledgeStrand 5 2 true

localYandruwandhaKnowledge : KnowledgeStrand
localYandruwandhaKnowledge = knowledgeStrand 1 5 false

record CrossKnowledgeUse : Set where
  constructor crossKnowledgeUse
  field
    indigenousAssistanceReceived : Bool
    indigenousKnowledgeFullyIntegrated : Bool
    localPreparationKnowledgeLost : Bool
    survivorSupportedByLocalCommunity : Bool

burkeWillsWitness : CrossKnowledgeUse
burkeWillsWitness = crossKnowledgeUse true false true true

data PrestigePromotesLocalCompetence : Set where

data OneFailurePromotesNeverUsedIndigenousKnowledge : Set where

data IndigenousAssistancePromotesInstitutionalIntegration : Set where

prestigeDoesNotPromoteLocalCompetence : PrestigePromotesLocalCompetence → ⊥
prestigeDoesNotPromoteLocalCompetence ()

oneFailureDoesNotPromoteNeverUsedIndigenousKnowledge :
  OneFailurePromotesNeverUsedIndigenousKnowledge → ⊥
oneFailureDoesNotPromoteNeverUsedIndigenousKnowledge ()

assistanceDoesNotPromoteInstitutionalIntegration :
  IndigenousAssistancePromotesInstitutionalIntegration → ⊥
assistanceDoesNotPromoteInstitutionalIntegration ()

record BurkeWillsSituatedKnowledgeBoundary : Set where
  constructor burkeWillsSituatedKnowledgeBoundary
  field
    formalInstitutionalPrestigeEqualsLocalCompetence : Bool
    expeditionReceivedIndigenousAssistance : Bool
    assistanceWasConsistentlyInstitutionalised : Bool
    localKnowledgeCouldBeLifePreserving : Bool
    singleExpeditionProvesUniversalColonialEpistemology : Bool

canonicalBurkeWillsSituatedKnowledgeBoundary : BurkeWillsSituatedKnowledgeBoundary
canonicalBurkeWillsSituatedKnowledgeBoundary =
  burkeWillsSituatedKnowledgeBoundary false true false true false
