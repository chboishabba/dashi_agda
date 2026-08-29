module DASHI.Governance.SmithResearchAgendaAuthorityBoundaryExact where

open import DASHI.Core.Prelude
import DASHI.Governance.IndigenousAuthoritySourceRegistryExact as Sources

------------------------------------------------------------------------
-- LINDA TUHIWAI SMITH: RESEARCH-AGENDA AUTHORITY BOUNDARY
--
-- Source: Linda Tuhiwai Smith, Decolonizing Methodologies: Research and
-- Indigenous Peoples, 3rd ed., Bloomsbury Academic (2022),
-- ISBN 9781350346086.  No DOI asserted for this edition.
--
-- Bounded conceptual role: authority over the research agenda/question is
-- separate from downstream empirical correctness or permission to reuse an
-- artifact.  The finite witness below is DASHI-owned formal machinery.
------------------------------------------------------------------------

data AgendaOrigin : Set where
  communityAgenda externalAgenda : AgendaOrigin

data DataQuality : Set where
  incorrectData correctData : DataQuality

data DownstreamUse : Set where
  downstreamUnauthorized downstreamAuthorized : DownstreamUse

data DecolonizingAgendaStatus : Set where
  agendaNotCommunityAuthorized agendaCommunityAuthorized : DecolonizingAgendaStatus

agendaStatus : AgendaOrigin → DecolonizingAgendaStatus
agendaStatus communityAgenda = agendaCommunityAuthorized
agendaStatus externalAgenda = agendaNotCommunityAuthorized

correctness : AgendaOrigin → DataQuality
correctness communityAgenda = correctData
correctness externalAgenda = correctData

reuseStatus : AgendaOrigin → DownstreamUse
reuseStatus communityAgenda = downstreamAuthorized
reuseStatus externalAgenda = downstreamAuthorized

sameCorrectness : correctness communityAgenda ≡ correctness externalAgenda
sameCorrectness = refl

sameDownstreamUse : reuseStatus communityAgenda ≡ reuseStatus externalAgenda
sameDownstreamUse = refl

differentAgendaAuthority : agendaStatus communityAgenda ≡ agendaStatus externalAgenda → ⊥
differentAgendaAuthority ()

correctDataDoesNotRecoverAgendaAuthority :
  correctness communityAgenda ≡ correctness externalAgenda →
  agendaStatus communityAgenda ≡ agendaStatus externalAgenda → ⊥
correctDataDoesNotRecoverAgendaAuthority _ = differentAgendaAuthority

downstreamAuthorizationDoesNotRecoverAgendaAuthority :
  reuseStatus communityAgenda ≡ reuseStatus externalAgenda →
  agendaStatus communityAgenda ≡ agendaStatus externalAgenda → ⊥
downstreamAuthorizationDoesNotRecoverAgendaAuthority _ = differentAgendaAuthority

smithSource : Sources.SourceReference
smithSource = Sources.smith2022

record SmithAgendaBoundary : Set where
  constructor smithAgendaBoundary
  field
    authorityOverAnswerEqualsAuthorityOverQuestion : Bool
    authorityOverAnswerEqualsAuthorityOverQuestionIsFalse :
      authorityOverAnswerEqualsAuthorityOverQuestion ≡ false
    correctDataImpliesCommunityAuthorizedAgenda : Bool
    correctDataImpliesCommunityAuthorizedAgendaIsFalse :
      correctDataImpliesCommunityAuthorizedAgenda ≡ false
    downstreamUseAuthorizationImpliesAgendaAuthorization : Bool
    downstreamUseAuthorizationImpliesAgendaAuthorizationIsFalse :
      downstreamUseAuthorizationImpliesAgendaAuthorization ≡ false
    sourceBookEndorsesDASHIEncoding : Bool
    sourceBookEndorsesDASHIEncodingIsFalse : sourceBookEndorsesDASHIEncoding ≡ false

canonicalSmithAgendaBoundary : SmithAgendaBoundary
canonicalSmithAgendaBoundary =
  smithAgendaBoundary false refl false refl false refl false refl
