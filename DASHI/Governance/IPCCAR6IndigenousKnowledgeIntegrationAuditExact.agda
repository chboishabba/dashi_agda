module DASHI.Governance.IPCCAR6IndigenousKnowledgeIntegrationAuditExact where

open import DASHI.Core.Prelude
import DASHI.Governance.IndigenousEnvironmentalJusticeSourceRegistryExact as Sources

------------------------------------------------------------------------
-- IPCC AR6: KNOWLEDGE-SYSTEM / CONSUMER / REPORT-PART ADEQUACY AUDIT
--
-- IPCC AR6 WGII (2022): inclusive adaptation planning can benefit from
-- scientific, Indigenous and local knowledge; Chapter 14 includes Indigenous
-- contributing authors and explicit Indigenous-knowledge assessment.
--
-- Pasang Yangjee Sherpa, "Relevance of the Sixth IPCC Assessment Report to
-- Indigenous lived realities", AlterNative 21(3), 2025,
-- DOI 10.1177/11771801251362621: systematic audit of uneven Indigenous
-- representation across AR6, with WGII much richer than WGI/WGIII.
------------------------------------------------------------------------

data KnowledgeKind : Set where
  scientificKnowledge indigenousKnowledge localKnowledge : KnowledgeKind

data AssessmentSurface : Set where
  wgIPhysicalScience wgIIImpactsAdaptation wgIIChapter14 wgIIInclusivePlanning wgIIIAmitigation : AssessmentSurface

data IntegrationLevel : Set where
  sparseReference substantiveIntegration indigenousAuthorship : IntegrationLevel

integration : AssessmentSurface → KnowledgeKind → IntegrationLevel
integration wgIPhysicalScience indigenousKnowledge = sparseReference
integration wgIIImpactsAdaptation indigenousKnowledge = substantiveIntegration
integration wgIIChapter14 indigenousKnowledge = indigenousAuthorship
integration wgIIInclusivePlanning indigenousKnowledge = substantiveIntegration
integration wgIIIAmitigation indigenousKnowledge = sparseReference
integration _ scientificKnowledge = substantiveIntegration
integration _ localKnowledge = substantiveIntegration

wgiiChapter14StrongerThanWgi :
  integration wgIIChapter14 indigenousKnowledge ≡ indigenousAuthorship
wgiiChapter14StrongerThanWgi = refl

wgiSparse : integration wgIPhysicalScience indigenousKnowledge ≡ sparseReference
wgiSparse = refl

wgiiiSparse : integration wgIIIAmitigation indigenousKnowledge ≡ sparseReference
wgiiiSparse = refl

ipccSource : Sources.SourceReference
ipccSource = Sources.ipccWGII2022

sherpaSource : Sources.SourceReference
sherpaSource = Sources.sherpa2025

record IPCCIndigenousKnowledgeBoundary : Set where
  constructor ipccIndigenousKnowledgeBoundary
  field
    ar6IntegrationUniformAcrossWorkingGroups : Bool
    ar6IntegrationUniformAcrossWorkingGroupsIsFalse : ar6IntegrationUniformAcrossWorkingGroups ≡ false
    indigenousKnowledgeIsOnlyValidForVulnerabilityConsumer : Bool
    indigenousKnowledgeIsOnlyValidForVulnerabilityConsumerIsFalse : indigenousKnowledgeIsOnlyValidForVulnerabilityConsumer ≡ false
    scientificKnowledgeSubsumesAllOtherKnowledgeByDefinition : Bool
    scientificKnowledgeSubsumesAllOtherKnowledgeByDefinitionIsFalse : scientificKnowledgeSubsumesAllOtherKnowledgeByDefinition ≡ false
    wgiiProgressClosesKnowledgeJusticeQuestion : Bool
    wgiiProgressClosesKnowledgeJusticeQuestionIsFalse : wgiiProgressClosesKnowledgeJusticeQuestion ≡ false
    sparseRepresentationMeansZeroEpistemicValue : Bool
    sparseRepresentationMeansZeroEpistemicValueIsFalse : sparseRepresentationMeansZeroEpistemicValue ≡ false

canonicalIPCCIndigenousKnowledgeBoundary : IPCCIndigenousKnowledgeBoundary
canonicalIPCCIndigenousKnowledgeBoundary =
  ipccIndigenousKnowledgeBoundary false refl false refl false refl false refl false refl
