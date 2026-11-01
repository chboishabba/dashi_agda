module DASHI.Core.InstitutionalProximityInfluenceAdequacyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- INSTITUTIONAL PROXIMITY / INFLUENCE ADEQUACY
--
-- Proximity is typed as an access/opportunity surface, not an influence or
-- corruption conclusion.  The finite witness shows that equal high-proximity
-- surfaces can coexist with different decision-influence answers.
------------------------------------------------------------------------

record ProximityProfile : Set where
  constructor proximityProfile
  field
    wealthResourceReference : String
    familyNetworkReference : String
    religiousNetworkReference : String
    professionalNetworkReference : String
    politicalAccessReference : String
    repeatPlayerReference : String
    reputationReference : String
    brokerAccessReference : String

open ProximityProfile public

data ProximityWorld : Set where
  highProximityInfluenceWorld : ProximityWorld
  highProximityNoInfluenceWorld : ProximityWorld

data ProximitySurface : Set where
  sameHighProximitySurface : ProximitySurface

data ProximityQuery : Set where
  proximityIdentityQuery : ProximityQuery
  influenceQuery : ProximityQuery

data ProximityAnswer : Set where
  sameProximityAnswer : ProximityAnswer
  influenceOccurred : ProximityAnswer
  influenceNotEstablished : ProximityAnswer

proximitySurface : ProximityWorld → ProximitySurface
proximitySurface world = sameHighProximitySurface

proximityAnswer : ProximityQuery → ProximityWorld → ProximityAnswer
proximityAnswer proximityIdentityQuery world = sameProximityAnswer
proximityAnswer influenceQuery highProximityInfluenceWorld = influenceOccurred
proximityAnswer influenceQuery highProximityNoInfluenceWorld = influenceNotEstablished

proximitySemantics : Query.QuerySemantics ProximityWorld ProximityQuery ProximityAnswer
proximitySemantics = Query.querySemantics proximityAnswer

proximityIdentityAdequate :
  Query.AdequateFor proximitySurface proximitySemantics proximityIdentityQuery
proximityIdentityAdequate =
  Query.factorsForQuery (λ surface → sameProximityAnswer) (λ world → refl)

InfluenceQueryAdequacyDefect : Set₁
InfluenceQueryAdequacyDefect =
  Query.QueryAdequacyDefect proximitySurface proximitySemantics influenceQuery

influenceQueryAdequacyDefect : InfluenceQueryAdequacyDefect
influenceQueryAdequacyDefect =
  Query.queryAdequacyDefect
    highProximityInfluenceWorld
    highProximityNoInfluenceWorld
    refl
    (λ ())

InfluenceThroughProximity : Set₁
InfluenceThroughProximity =
  Query.AdequateFor proximitySurface proximitySemantics influenceQuery

influenceDoesNotFactorThroughProximity : InfluenceThroughProximity → ⊥
influenceDoesNotFactorThroughProximity =
  Query.queryAdequacyDefectBlocksFactorisation influenceQueryAdequacyDefect

record InstitutionalProximityBoundary : Set where
  constructor institutionalProximityBoundary
  field
    proximityAutomaticallyInfluence : Bool
    accessAutomaticallyDecisionControl : Bool
    networkMembershipAutomaticallyMoralReliability : Bool
    donationAutomaticallyQuidProQuo : Bool
    brokerRelationshipAutomaticallyCorruption : Bool
    repeatPlayerStatusAutomaticallyEpistemicAuthority : Bool
    absenceOfRecordedAccessAutomaticallyAbsenceOfInfluence : Bool
    proximityMayRemainRelevantAcquisitionCoordinate : Bool
    influenceRequiresSeparateEvidence : Bool

open InstitutionalProximityBoundary public

canonicalInstitutionalProximityBoundary : InstitutionalProximityBoundary
canonicalInstitutionalProximityBoundary =
  institutionalProximityBoundary
    false
    false
    false
    false
    false
    false
    false
    true
    true
