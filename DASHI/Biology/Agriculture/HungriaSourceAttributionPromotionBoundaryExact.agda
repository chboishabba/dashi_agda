module DASHI.Biology.Agriculture.HungriaSourceAttributionPromotionBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.Agriculture.HungriaBiologicalNitrogenFixationSourceAtlas as Sources

------------------------------------------------------------------------
-- HUNGRIA AGRICULTURE SOURCE ATTRIBUTION / PROMOTION BOUNDARY
--
-- Retrospective cross-pollination from the repository's established source
-- discipline.  This module does NOT import a draft economics PR and does NOT
-- attribute these DASHI datatypes or theorem shapes to Hungria, Telles,
-- Nogueira, Embrapa, the World Food Prize Foundation, or any external author.
--
-- Layers remain distinct:
--
--   primary/source proposition
--   != secondary or institutional report
--   != DASHI bounded interpretation
--   != DASHI formal construction
--   != DASHI theorem
--   != empirical promotion
--   != system-wide/generalized classification.
------------------------------------------------------------------------

data AttributionLayer : Set where
  primarySourceProposition : AttributionLayer
  institutionalReport : AttributionLayer
  attributedSpeakerProposition : AttributionLayer
  dashiBoundedInterpretation : AttributionLayer
  dashiFormalConstruction : AttributionLayer
  dashiTheorem : AttributionLayer
  empiricalPromotion : AttributionLayer
  generalizedAgronomicClaim : AttributionLayer


data AccessCarrierRole : Set where
  canonicalPublication : AccessCarrierRole
  authorOrInstitutionRepository : AccessCarrierRole
  institutionalNewsCarrier : AccessCarrierRole
  institutionalRetrospectiveCarrier : AccessCarrierRole
  accessMirrorOnly : AccessCarrierRole

record SourceAttributionReceipt : Set where
  constructor sourceAttributionReceipt
  field
    source : Sources.BNFSource
    upstreamAuthors : String
    speakerOrClaimOwner : String
    publicationCarrier : String
    canonicalPublicationLocation : String
    accessLocation : String
    accessCarrierRole : AccessCarrierRole
    exactSourceLocation : String
    boundedProposition : String
    attributionLayer : AttributionLayer
    formalisationOwner : String
    promotionAuthority : String

open SourceAttributionReceipt public

------------------------------------------------------------------------
-- Exact current receipts.
------------------------------------------------------------------------

telles2023ModelReceipt : SourceAttributionReceipt
telles2023ModelReceipt =
  sourceAttributionReceipt
    Sources.tellesNogueiraHungria2023
    "Tiago Santos Telles; Marco Antonio Nogueira; Mariangela Hungria"
    "Telles, Nogueira and Hungria as article authors"
    "Environmental Technology & Innovation 31 (2023) 103158"
    "Elsevier journal record, DOI 10.1016/j.eti.2023.103158"
    "Embrapa Alice institutional repository copy"
    authorOrInstitutionRepository
    "Article abstract, methods/equations, tables and reported 2019-2020 outputs"
    "The paper reports and models Brazilian soybean BNF economic value and GHG mitigation for the source-defined seasons and assumptions"
    primarySourceProposition
    "DASHI"
    "Authority limited to the paper's stated model, assumptions, data lineage and reported outputs"

embrapa2025SavingsReceipt : SourceAttributionReceipt
embrapa2025SavingsReceipt =
  sourceAttributionReceipt
    Sources.embrapa2025PrizeNews
    "Embrapa institutional news publication"
    "Embrapa publication voice for the savings sentence"
    "Embrapa Portal / Embrapa Soja news item, 16 October 2025"
    "Embrapa Portal"
    "Embrapa Portal English-language page"
    institutionalNewsCarrier
    "Paragraph reporting co-inoculation adoption and 2024 savings"
    "In 2024, estimated savings from not using nitrogen fertilizers were about USD 25 billion"
    institutionalReport
    "DASHI"
    "Reports the estimate; does not itself expose the complete 2024 calculation replay"

embrapa2025MitigationQuoteReceipt : SourceAttributionReceipt
embrapa2025MitigationQuoteReceipt =
  sourceAttributionReceipt
    Sources.embrapa2025PrizeNews
    "Embrapa institutional news publication"
    "Mariangela Hungria, quoted speaker"
    "Embrapa Portal / Embrapa Soja news item, 16 October 2025"
    "Embrapa Portal"
    "Embrapa Portal English-language page"
    institutionalNewsCarrier
    "Same paragraph; sentence introduced as Hungria states"
    "Use of the bacteria helped mitigate more than 230 million tonnes CO2-equivalent in 2024"
    attributedSpeakerProposition
    "DASHI"
    "Speaker attribution is recovered; calculation replay and independent verification remain separate obligations"

worldFoodPrize2025Receipt : SourceAttributionReceipt
worldFoodPrize2025Receipt =
  sourceAttributionReceipt
    Sources.worldFoodPrize2025
    "World Food Prize Foundation"
    "World Food Prize Foundation institutional publication voice"
    "2025 Laureate biography / laureate brochure"
    "World Food Prize Foundation"
    "World Food Prize Foundation web page / brochure"
    institutionalRetrospectiveCarrier
    "Laureate biography paragraphs summarizing adoption, savings and emissions"
    "Technologies associated with Hungria's programme are described as used at large scale and associated with roughly USD 25 billion annual savings and 230 million metric tons CO2-equivalent avoided"
    institutionalReport
    "DASHI"
    "Retrospective corroborating carrier, not a substitute for primary calculation provenance"

------------------------------------------------------------------------
-- Promotion chain.  Every stronger claim needs a producer for that arrow.
------------------------------------------------------------------------

record PromotionStepReceipt : Set₁ where
  constructor promotionStepReceipt
  field
    fromLayer : AttributionLayer
    toLayer : AttributionLayer
    upstreamReceipt : SourceAttributionReceipt
    PromotionProducer : Set
    promotionProducer : PromotionProducer
    preservesClaimOwner : Bool
    preservesBoundedProposition : Bool
    authorityForThisStep : String

open PromotionStepReceipt public

------------------------------------------------------------------------
-- Firewalls carried over from previous source-attribution work.
------------------------------------------------------------------------

data AccessCarrierImpliesAuthorshipPermission : Set where

data InstitutionalPublicationImpliesEverySentenceHungriaOwnedPermission : Set where

data SourceArgumentImpliesDASHIFormalisationOwnershipPermission : Set where

data InstitutionalReportImpliesPrimaryCalculationAuthorityPermission : Set where

data SameNumbersImpliesSameProducerPermission : Set where

data SameContentImpliesIndependentProducerPermission : Set where

data SourceReceiptImpliesPromotionStepPermission : Set where

data OneProducerPaysAllLaterStagesPermission : Set where

data SpeakerQuoteImpliesCalculationReplayPermission : Set where

accessCarrierDoesNotAutoPromoteToAuthorship :
  AccessCarrierImpliesAuthorshipPermission → ⊥
accessCarrierDoesNotAutoPromoteToAuthorship ()

institutionalPublicationDoesNotMakeEverySentenceHungriaOwned :
  InstitutionalPublicationImpliesEverySentenceHungriaOwnedPermission → ⊥
institutionalPublicationDoesNotMakeEverySentenceHungriaOwned ()

sourceArgumentDoesNotTransferDASHIOwnership :
  SourceArgumentImpliesDASHIFormalisationOwnershipPermission → ⊥
sourceArgumentDoesNotTransferDASHIOwnership ()

institutionalReportDoesNotBecomePrimaryCalculation :
  InstitutionalReportImpliesPrimaryCalculationAuthorityPermission → ⊥
institutionalReportDoesNotBecomePrimaryCalculation ()

sameNumbersDoNotIdentifyProducer :
  SameNumbersImpliesSameProducerPermission → ⊥
sameNumbersDoNotIdentifyProducer ()

sameContentDoesNotEstablishIndependentProducer :
  SameContentImpliesIndependentProducerPermission → ⊥
sameContentDoesNotEstablishIndependentProducer ()

sourceReceiptDoesNotPayPromotion :
  SourceReceiptImpliesPromotionStepPermission → ⊥
sourceReceiptDoesNotPayPromotion ()

oneProducerDoesNotPayAllLaterStages :
  OneProducerPaysAllLaterStagesPermission → ⊥
oneProducerDoesNotPayAllLaterStages ()

speakerQuoteDoesNotSupplyCalculationReplay :
  SpeakerQuoteImpliesCalculationReplayPermission → ⊥
speakerQuoteDoesNotSupplyCalculationReplay ()
