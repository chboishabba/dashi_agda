module DASHI.Culture.AmyEskridgeHAL5AntigravitySourceEntitlementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.AmyEskridgeFirstPersonClaimCarrierExact as Claim

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: SOURCE-ENTITLED 2018 ANTIGRAVITY TALK
--
-- This owner records only what the HAL5-hosted program/deck entitles us to
-- attribute to Amy.  It does not retroactively identify every modern DASHI
-- mechanism family as Amy's own theory.
------------------------------------------------------------------------

record HAL5TalkSourceReceipt : Set where
  constructor hal5-talk-source-receipt
  field
    speaker : String
    eventDate : String
    host : String
    title : String
    programLocator : String
    chartsLocator : String
    instituteRole : String
    gravityModificationNamed : Bool
    negativeMassDiscussed : Bool
    liTorrDiscussed : Bool
    superconductivityDiscussed : Bool

open HAL5TalkSourceReceipt public

canonicalHAL5TalkSourceReceipt : HAL5TalkSourceReceipt
canonicalHAL5TalkSourceReceipt =
  hal5-talk-source-receipt
    "Amy Eskridge"
    "2018-12-06"
    "Huntsville Alabama L5 Society (HAL5)"
    "A Historical Perspective on Anti-Gravity Technology"
    "https://www.hal5.org/program-2018-12.shtml"
    "HAL5 December 2018 charts linked from the official program/archive page"
    "President and Co-founder, The Institute for Exotic Science"
    true true true true

amyHAL5AntigravityClaim : Claim.FirstPersonClaimCarrier
amyHAL5AntigravityClaim =
  Claim.first-person-claim-carrier
    "Amy Eskridge"
    Claim.antigravityResearchStatement
    Claim.archivedRecording
    "HAL5 December 2018 program and presentation charts"
    "presentation sections defining antigravity, discussing negative mass, and presenting Li-Torr superconducting gravity"
    "Amy publicly presented negative mass and Li-Torr superconducting gravity as historical antigravity research topics"
    Claim.independentlyCorroborated

record HAL5AttributionBoundary : Set where
  constructor hal5-attribution-boundary
  field
    amyDiscussedLiTorr : Bool
    amyDiscussedNegativeMass : Bool
    amyDiscussedSuperconductingGravity : Bool
    discussionEqualsPersonalEndorsement : Bool
    discussionEqualsModernMaterialEffectiveNegativeGTheory : Bool
    talkMaySeedBackwardPrimaryLiteratureSearch : Bool
    modernMechanismAttributionStillNeedsExactAmyStatement : Bool

canonicalHAL5AttributionBoundary : HAL5AttributionBoundary
canonicalHAL5AttributionBoundary =
  hal5-attribution-boundary true true true false false true true
