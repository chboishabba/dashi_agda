module DASHI.Reasoning.SensibLawEncyclopediaAttributedSourceBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attributed
import DASHI.Reasoning.SensibLawEncyclopediaCorpusClaimReceiptExact as Encyclopedia

------------------------------------------------------------------------
-- ENCYCLOPEDIA CLAIM -> CANONICAL ATTRIBUTED SOURCE BINDING
--
-- The edition/passsage receipt says what a bounded encyclopedia carrier says.
-- AttributedSource records bibliographic/source identity.  This bridge binds
-- the two without promoting either to truth or consumer-specific authority.
-- Full empirical diligence remains downstream.
------------------------------------------------------------------------

record EncyclopediaAttributedSourceBinding : Set where
  constructor encyclopedia-attributed-source-binding
  field
    claim : Encyclopedia.CorpusClaimReceipt
    attributedSource : Attributed.AttributedSource
    sameSourceReference : String
    editionIdentityReference : String
    exactPassageLocatorReference : String
    attributionAssessmentReference : String

open EncyclopediaAttributedSourceBinding public

------------------------------------------------------------------------
-- Explicit downstream state: bibliographic binding is not diligence.
------------------------------------------------------------------------

data EncyclopediaSourceUseStatus : Set where
  sourceBoundOnly : EncyclopediaSourceUseStatus
  diligenceRequired : EncyclopediaSourceUseStatus
  consumerAssessmentRequired : EncyclopediaSourceUseStatus

record EncyclopediaSourceUseResidual : Set where
  constructor encyclopedia-source-use-residual
  field
    binding : EncyclopediaAttributedSourceBinding
    status : EncyclopediaSourceUseStatus
    consumerReference : String
    residualReference : String

open EncyclopediaSourceUseResidual public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data AttributedBindingCreatesWorldTruth : Set where
data AttributedBindingPaysConsumerAuthority : Set where
data AttributedBindingEqualsSourceDiligence : Set where
data EditorialReputationPaysExactPropositionSupport : Set where

attributedBindingDoesNotCreateWorldTruth :
  AttributedBindingCreatesWorldTruth → ⊥
attributedBindingDoesNotCreateWorldTruth ()

attributedBindingDoesNotPayConsumerAuthority :
  AttributedBindingPaysConsumerAuthority → ⊥
attributedBindingDoesNotPayConsumerAuthority ()

attributedBindingDoesNotEqualDiligence :
  AttributedBindingEqualsSourceDiligence → ⊥
attributedBindingDoesNotEqualDiligence ()

editorialReputationDoesNotPayExactPropositionSupport :
  EditorialReputationPaysExactPropositionSupport → ⊥
editorialReputationDoesNotPayExactPropositionSupport ()

record EncyclopediaAttributedSourceBoundary : Set where
  constructor encyclopedia-attributed-source-boundary
  field
    encyclopediaClaimMayBindCanonicalAttributedSource : Bool
    encyclopediaClaimMayBindCanonicalAttributedSourceIsTrue :
      encyclopediaClaimMayBindCanonicalAttributedSource ≡ true
    attributedBindingCreatesTruth : Bool
    attributedBindingCreatesTruthIsFalse :
      attributedBindingCreatesTruth ≡ false
    attributedBindingPaysConsumerAuthority : Bool
    attributedBindingPaysConsumerAuthorityIsFalse :
      attributedBindingPaysConsumerAuthority ≡ false
    fullDiligenceRemainsDownstream : Bool
    fullDiligenceRemainsDownstreamIsTrue :
      fullDiligenceRemainsDownstream ≡ true

canonicalEncyclopediaAttributedSourceBoundary :
  EncyclopediaAttributedSourceBoundary
canonicalEncyclopediaAttributedSourceBoundary =
  encyclopedia-attributed-source-boundary
    true refl false refl false refl true refl
