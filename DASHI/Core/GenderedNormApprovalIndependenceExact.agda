module DASHI.Core.GenderedNormApprovalIndependenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- GENDERED-NORM / APPROVAL-INDEPENDENCE STRUCTURAL CORE
--
-- This module does NOT prove an empirical theory of patriarchy, women,
-- likability, fear, respect, loyalty, or social sanctions.
--
-- It isolates three finite logical distinctions used by the supplied source:
--
--   (1) reward for a trait does not determine whether refusal is sanctioned;
--   (2) a likability surface does not determine respect;
--   (3) a likability surface does not determine loyalty.
--
-- Those are structural non-factorability results.  Applying them to a real
-- institution or population requires separately sourced empirical premises.
------------------------------------------------------------------------

data ProtocolWorld : Set where
  rewardWithoutRefusalSanction : ProtocolWorld
  rewardWithRefusalSanction : ProtocolWorld

data RelatabilityRewardSurface : Set where
  sameRelatabilityReward : RelatabilityRewardSurface

data RefusalSanctionQuery : Set where
  refusalSanctionQuery : RefusalSanctionQuery

data RefusalSanctionAnswer : Set where
  noRefusalSanction : RefusalSanctionAnswer
  refusalIsSanctioned : RefusalSanctionAnswer

relatabilityRewardSurface : ProtocolWorld → RelatabilityRewardSurface
relatabilityRewardSurface world = sameRelatabilityReward

refusalSanctionAnswer :
  RefusalSanctionQuery → ProtocolWorld → RefusalSanctionAnswer
refusalSanctionAnswer refusalSanctionQuery rewardWithoutRefusalSanction =
  noRefusalSanction
refusalSanctionAnswer refusalSanctionQuery rewardWithRefusalSanction =
  refusalIsSanctioned

refusalSanctionSemantics :
  Query.QuerySemantics ProtocolWorld RefusalSanctionQuery RefusalSanctionAnswer
refusalSanctionSemantics = Query.querySemantics refusalSanctionAnswer

RelatabilityRewardCannotDetermineRefusalSanction : Set₁
RelatabilityRewardCannotDetermineRefusalSanction =
  Query.QueryAdequacyDefect
    relatabilityRewardSurface
    refusalSanctionSemantics
    refusalSanctionQuery

relatabilityRewardCannotDetermineRefusalSanction :
  RelatabilityRewardCannotDetermineRefusalSanction
relatabilityRewardCannotDetermineRefusalSanction =
  Query.queryAdequacyDefect
    rewardWithoutRefusalSanction
    rewardWithRefusalSanction
    refl
    (λ ())

RelatabilityRewardAdequateForRefusalSanction : Set₁
RelatabilityRewardAdequateForRefusalSanction =
  Query.AdequateFor
    relatabilityRewardSurface
    refusalSanctionSemantics
    refusalSanctionQuery

relatabilityRewardDoesNotEntailRefusalSanction :
  RelatabilityRewardAdequateForRefusalSanction → ⊥
relatabilityRewardDoesNotEntailRefusalSanction =
  Query.queryAdequacyDefectBlocksFactorisation
    relatabilityRewardCannotDetermineRefusalSanction

------------------------------------------------------------------------
-- Likability does not determine respect.
------------------------------------------------------------------------

data LikeRespectWorld : Set where
  likedLowRespect : LikeRespectWorld
  likedHighRespect : LikeRespectWorld

data LikabilitySurface : Set where
  sameLikability : LikabilitySurface

data RespectQuery : Set where
  respectQuery : RespectQuery

data RespectAnswer : Set where
  lowerRespect : RespectAnswer
  higherRespect : RespectAnswer

likabilitySurface : LikeRespectWorld → LikabilitySurface
likabilitySurface world = sameLikability

respectAnswer : RespectQuery → LikeRespectWorld → RespectAnswer
respectAnswer respectQuery likedLowRespect = lowerRespect
respectAnswer respectQuery likedHighRespect = higherRespect

respectSemantics :
  Query.QuerySemantics LikeRespectWorld RespectQuery RespectAnswer
respectSemantics = Query.querySemantics respectAnswer

LikabilityCannotDetermineRespect : Set₁
LikabilityCannotDetermineRespect =
  Query.QueryAdequacyDefect likabilitySurface respectSemantics respectQuery

likabilityCannotDetermineRespect : LikabilityCannotDetermineRespect
likabilityCannotDetermineRespect =
  Query.queryAdequacyDefect likedLowRespect likedHighRespect refl (λ ())

LikabilityAdequateForRespect : Set₁
LikabilityAdequateForRespect =
  Query.AdequateFor likabilitySurface respectSemantics respectQuery

likabilityDoesNotDetermineRespect : LikabilityAdequateForRespect → ⊥
likabilityDoesNotDetermineRespect =
  Query.queryAdequacyDefectBlocksFactorisation likabilityCannotDetermineRespect

------------------------------------------------------------------------
-- Likability does not determine loyalty.
------------------------------------------------------------------------

data LikeLoyaltyWorld : Set where
  likedLowLoyalty : LikeLoyaltyWorld
  likedHighLoyalty : LikeLoyaltyWorld

data LoyaltyQuery : Set where
  loyaltyQuery : LoyaltyQuery

data LoyaltyAnswer : Set where
  lowerLoyalty : LoyaltyAnswer
  higherLoyalty : LoyaltyAnswer

likabilityLoyaltySurface : LikeLoyaltyWorld → LikabilitySurface
likabilityLoyaltySurface world = sameLikability

loyaltyAnswer : LoyaltyQuery → LikeLoyaltyWorld → LoyaltyAnswer
loyaltyAnswer loyaltyQuery likedLowLoyalty = lowerLoyalty
loyaltyAnswer loyaltyQuery likedHighLoyalty = higherLoyalty

loyaltySemantics :
  Query.QuerySemantics LikeLoyaltyWorld LoyaltyQuery LoyaltyAnswer
loyaltySemantics = Query.querySemantics loyaltyAnswer

LikabilityCannotDetermineLoyalty : Set₁
LikabilityCannotDetermineLoyalty =
  Query.QueryAdequacyDefect
    likabilityLoyaltySurface
    loyaltySemantics
    loyaltyQuery

likabilityCannotDetermineLoyalty : LikabilityCannotDetermineLoyalty
likabilityCannotDetermineLoyalty =
  Query.queryAdequacyDefect likedLowLoyalty likedHighLoyalty refl (λ ())

LikabilityAdequateForLoyalty : Set₁
LikabilityAdequateForLoyalty =
  Query.AdequateFor likabilityLoyaltySurface loyaltySemantics loyaltyQuery

likabilityDoesNotDetermineLoyalty : LikabilityAdequateForLoyalty → ⊥
likabilityDoesNotDetermineLoyalty =
  Query.queryAdequacyDefectBlocksFactorisation likabilityCannotDetermineLoyalty

------------------------------------------------------------------------
-- Non-promotion boundary.
------------------------------------------------------------------------

record GenderedNormApprovalBoundary : Set where
  constructor genderedNormApprovalBoundary
  field
    sourceTranscriptAutomaticallyEstablishesPatriarchyMechanism : Bool
    rewardForRelatabilityAutomaticallyImpliesSanctionForRefusal : Bool
    likabilityAutomaticallyImpliesRespect : Bool
    likabilityAutomaticallyImpliesLoyalty : Bool
    fearAutomaticallyIdenticalToRespect : Bool
    machiavelliAppealAutomaticallyProvesStrategy : Bool
    softwareMetaphorAutomaticallyIdentifiesLiteralBackend : Bool
    structuralCollisionCanRefuteLogicalEntailment : Bool
    empiricalApplicationRequiresExternalEvidence : Bool
    sourceClaimAndRepositoryTheoremRemainDistinct : Bool

open GenderedNormApprovalBoundary public

canonicalGenderedNormApprovalBoundary : GenderedNormApprovalBoundary
canonicalGenderedNormApprovalBoundary =
  genderedNormApprovalBoundary
    false
    false
    false
    false
    false
    false
    false
    true
    true
    true
