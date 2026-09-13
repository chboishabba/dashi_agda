module DASHI.Culture.AmyEskridgeHAL5AntigravitySourceEntitlementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.AmyEskridgeFirstPersonClaimCarrierExact as Claim

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: SOURCE-ENTITLED 2018 ANTIGRAVITY TALK
--
-- This owner records only what the HAL5-hosted program/deck entitles us to
-- attribute to Amy. It does not retroactively identify every modern DASHI
-- mechanism family as Amy's own theory, and host-authenticated presentation
-- content is not independent validation of the underlying physics.
------------------------------------------------------------------------

record HAL5TalkSourceReceipt : Set where
  constructor hal5-talk-source-receipt
  field
    speaker : String
    eventDate : String
    host : String
    title : String
    programLocator : String
    deckLocator : String
    instituteRole : String
    negativeMassDeckCoordinate : String
    liTorrDeckCoordinate : String
    conclusionDeckCoordinate : String
    gravityModificationNamed : Bool
    negativeMassDiscussed : Bool
    liTorrDiscussed : Bool
    superconductivityDiscussed : Bool
    testableHypothesisRequested : Bool
    independentFundingRequested : Bool

open HAL5TalkSourceReceipt public

canonicalHAL5TalkSourceReceipt : HAL5TalkSourceReceipt
canonicalHAL5TalkSourceReceipt =
  hal5-talk-source-receipt
    "Amy Eskridge"
    "2018-12-06"
    "Huntsville Alabama L5 Society (HAL5)"
    "A Historical Perspective on Anti-Gravity Technology"
    "https://www.hal5.org/program-2018-12.shtml"
    "https://www.hal5.org/PDF/HAL5-Dec2018-Talk-AntiGravity.pdf"
    "President and Co-founder, The Institute for Exotic Science"
    "deck page 6: negative mass / repulsive-force historical framing"
    "deck page 24 in PDF viewer: Ning Li & Doug Torr AC Gravity (1990's), superconducting ion-spin / gravitomagnetic / gravitoelectric description"
    "deck page 34 in PDF viewer: conclusion calls for theories with a testable hypothesis and independently funded private research"
    true true true true true true

amyHAL5AntigravityClaim : Claim.FirstPersonClaimCarrier
amyHAL5AntigravityClaim =
  Claim.first-person-claim-carrier
    "Amy Eskridge"
    Claim.antigravityResearchStatement
    Claim.archivedRecording
    "HAL5-hosted official 2018 program + HAL5-Dec2018-Talk-AntiGravity.pdf"
    "negative-mass section; Ning Li & Doug Torr AC Gravity slide; conclusion"
    "Amy publicly presented negative mass and Li-Torr superconducting gravity as historical antigravity research topics and called for testable hypotheses"
    Claim.independentlyCorroborated

record HAL5AttributionBoundary : Set where
  constructor hal5-attribution-boundary
  field
    amyDiscussedLiTorr : Bool
    amyDiscussedNegativeMass : Bool
    amyDiscussedSuperconductingGravity : Bool
    amyCalledForTestableHypotheses : Bool
    discussionEqualsPersonalEndorsement : Bool
    discussionEqualsModernMaterialEffectiveNegativeGTheory : Bool
    hostAuthenticatedDeckEqualsIndependentPhysicsValidation : Bool
    talkMaySeedBackwardPrimaryLiteratureSearch : Bool
    modernMechanismAttributionStillNeedsExactAmyStatement : Bool

canonicalHAL5AttributionBoundary : HAL5AttributionBoundary
canonicalHAL5AttributionBoundary =
  hal5-attribution-boundary true true true true false false false true true
