module DASHI.Culture.RastafariItalIndigenousKnowledgeDirectReuseExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as Indigenous
import DASHI.Culture.RastafariItalLivityExact as Ital

------------------------------------------------------------------------
-- DIRECT REUSE OF THE MERGED INDIGENOUS KNOWLEDGE CAPSTONE
--
-- The Indigenous owner remains authoritative for its own source-bounded
-- knowledge carrier.  This module does not translate its cultural content into
-- Rastafari content.  It only reuses the already-proved generic warning that a
-- detached proposition can erase provenance, authority, permission and
-- obligation.
------------------------------------------------------------------------

indigenousPropositionCannotRecoverProvenance :
  NonFactor.FactorsThrough
    Indigenous.extractedProposition
    Indigenous.carrierProvenance → ⊥
indigenousPropositionCannotRecoverProvenance =
  Indigenous.propositionCannotRecoverProvenance

indigenousPropositionCannotRecoverAuthority :
  NonFactor.FactorsThrough
    Indigenous.extractedProposition
    Indigenous.authority → ⊥
indigenousPropositionCannotRecoverAuthority =
  Indigenous.propositionCannotRecoverAuthority

indigenousPropositionCannotRecoverPermission :
  NonFactor.FactorsThrough
    Indigenous.extractedProposition
    Indigenous.permission → ⊥
indigenousPropositionCannotRecoverPermission =
  Indigenous.propositionCannotRecoverPermission

indigenousPropositionCannotRecoverObligation :
  NonFactor.FactorsThrough
    Indigenous.extractedProposition
    Indigenous.obligation → ⊥
indigenousPropositionCannotRecoverObligation =
  Indigenous.propositionCannotRecoverObligation

------------------------------------------------------------------------
-- Cross-cultural no-promotion.
------------------------------------------------------------------------

data ItalLivityIsIndigenousKnowledgeCarrier : Set where

data IndigenousReciprocityDefinesItalLivity : Set where

data ItalNaturalnessDefinesIndigenousAuthority : Set where

italLivityIsNotPromotedToIndigenousKnowledgeCarrier :
  ItalLivityIsIndigenousKnowledgeCarrier → ⊥
italLivityIsNotPromotedToIndigenousKnowledgeCarrier ()

indigenousReciprocityDoesNotDefineItalLivity :
  IndigenousReciprocityDefinesItalLivity → ⊥
indigenousReciprocityDoesNotDefineItalLivity ()

italNaturalnessDoesNotDefineIndigenousAuthority :
  ItalNaturalnessDefinesIndigenousAuthority → ⊥
italNaturalnessDoesNotDefineIndigenousAuthority ()

------------------------------------------------------------------------
-- The useful common rule is methodological, not doctrinal:
-- retain the situated coordinates required by the consumer instead of
-- flattening either tradition to a generic ecological-care proposition.
------------------------------------------------------------------------

record ItalIndigenousDirectReuseBoundary : Set where
  constructor italIndigenousDirectReuseBoundary
  field
    indigenousOwnerReusedWithoutCulturalFusion : Bool
    indigenousOwnerReusedWithoutCulturalFusionIsTrue :
      indigenousOwnerReusedWithoutCulturalFusion ≡ true

    detachedPropositionIsCompleteSituatedCarrier : Bool
    detachedPropositionIsCompleteSituatedCarrierIsFalse :
      detachedPropositionIsCompleteSituatedCarrier ≡ false

    sharedEcologicalConcernMeansSharedCulturalAuthority : Bool
    sharedEcologicalConcernMeansSharedCulturalAuthorityIsFalse :
      sharedEcologicalConcernMeansSharedCulturalAuthority ≡ false

canonicalItalIndigenousDirectReuseBoundary :
  ItalIndigenousDirectReuseBoundary
canonicalItalIndigenousDirectReuseBoundary =
  italIndigenousDirectReuseBoundary true refl false refl false refl
