module DASHI.Law.SensibLawHousingPossessionOrderSourceEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawHousingEpisodeEvidenceLineageExact as Housing

------------------------------------------------------------------------
-- PRIMARY TRIBUNAL SOURCE -> POSSESSION / TERMINATION OUTCOME
--
-- A notice-to-leave source defines/records a pre-tribunal process state.
-- A tribunal decision/order is a different source role which can establish a
-- possession/termination outcome in the particular tenancy.  One cannot be
-- promoted into the other by date or procedural sequence alone.
------------------------------------------------------------------------

data PossessionOutcome : Set where
  possessionOrderGranted : PossessionOutcome
  possessionOrderRefused : PossessionOutcome
  possessionOutcomeUnresolved : PossessionOutcome

record PossessionOrderSource : Set₁ where
  constructor possessionOrderSource
  field
    episodeReference : String
    tribunalReference : String
    decisionDateReference : String
    orderReference : String
    outcome : PossessionOutcome
    primarySourceReceipt : Set

open PossessionOrderSource public

record EpisodePossessionWeld
    (episode : Housing.HousingEpisode)
    (order : PossessionOrderSource) : Set₁ where
  constructor episodePossessionWeld
  field
    sameEpisodeReceipt : Set
    samePremisesReceipt : Set
    tribunalOrderAddsPossessionProcessStateReceipt : Set
    weldReference : String

open EpisodePossessionWeld public

record PossessionOrderBoundary : Set where
  constructor possessionOrderBoundary
  field
    noticeToLeaveAutomaticallyProvesPossessionOrder : Bool
    noticeToLeaveAutomaticallyProvesPossessionOrderIsFalse :
      noticeToLeaveAutomaticallyProvesPossessionOrder ≡ false
    partyEmailAutomaticallyEqualsTribunalOrder : Bool
    partyEmailAutomaticallyEqualsTribunalOrderIsFalse :
      partyEmailAutomaticallyEqualsTribunalOrder ≡ false
    tribunalDecisionMayEstablishPossessionOutcome : Bool
    tribunalDecisionMayEstablishPossessionOutcomeIsTrue :
      tribunalDecisionMayEstablishPossessionOutcome ≡ true
    possessionOutcomeAutomaticallyProvesUnderlyingWrongdoing : Bool
    possessionOutcomeAutomaticallyProvesUnderlyingWrongdoingIsFalse :
      possessionOutcomeAutomaticallyProvesUnderlyingWrongdoing ≡ false

canonicalPossessionOrderBoundary : PossessionOrderBoundary
canonicalPossessionOrderBoundary =
  possessionOrderBoundary false refl false refl true refl false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data NoticeAutomaticallyPossessionOrder : Set where
data PartyEmailAutomaticallyPrimaryTribunalOrder : Set where
data PossessionOrderAutomaticallyUnderlyingWrongdoing : Set where

noticeDoesNotAutoProvePossessionOrder : NoticeAutomaticallyPossessionOrder → ⊥
noticeDoesNotAutoProvePossessionOrder ()

partyEmailDoesNotAutoBecomePrimaryTribunalOrder :
  PartyEmailAutomaticallyPrimaryTribunalOrder → ⊥
partyEmailDoesNotAutoBecomePrimaryTribunalOrder ()

possessionOrderDoesNotAutoProveUnderlyingWrongdoing :
  PossessionOrderAutomaticallyUnderlyingWrongdoing → ⊥
possessionOrderDoesNotAutoProveUnderlyingWrongdoing ()

------------------------------------------------------------------------
-- Brighton bounded source fixture.
--
-- The QCAT correspondence of 2 June 2023 transmits the decisions in T22/23.
-- The amended decision states that paragraph 6 of the 21 April 2023 order is
-- amended so the tenants can remain rent-free from 21 April 2023 until the
-- date of execution of the warrant.  Separate contemporaneous QCAT-thread
-- correspondence records that a warrant of possession had issued and was to
-- operate from 5 June.  This closes existence of a possession-order outcome,
-- while the exact original 21-April warrant document remains a distinct source
-- carrier if later recovered.
------------------------------------------------------------------------

brightonPossessionOrder : PossessionOrderSource
brightonPossessionOrder =
  possessionOrderSource
    "17 Gordon Street Brighton tenancy displacement episode"
    "QCAT MCD Residential tenancy dispute T22/23 / Sandgate Claim 0000022/23"
    "21 April 2023 order; amended 2 June 2023"
    "amended paragraph 6: tenants remain rent-free until execution of the warrant"
    possessionOrderGranted
    ⊤

------------------------------------------------------------------------
-- Chapel Hill primary tribunal fixture.
--
-- Q243-25 decision, Adjudicator Murphy, 5 February 2025:
-- tenancy terminated from midnight 13 February 2025; warrant of possession to
-- issue for 50 Tucker Street; warrant takes effect 17 February 2025 and expires
-- 3 March 2025; execution as soon as reasonably practical after taking effect.
------------------------------------------------------------------------

chapelHillPossessionOrder : PossessionOrderSource
chapelHillPossessionOrder =
  possessionOrderSource
    "50 Tucker Street Chapel Hill housing/QCAT episode"
    "QCAT Q243-25"
    "5 February 2025"
    "termination from 13 February 2025; warrant of possession effective 17 February to 3 March 2025"
    possessionOrderGranted
    ⊤

record RecoveredPossessionOrderFixture : Set where
  constructor recoveredPossessionOrderFixture
  field
    brightonOrder : PossessionOrderSource
    chapelHillOrder : PossessionOrderSource
    brightonPossessionOutcomeClosed : Bool
    brightonPossessionOutcomeClosedIsTrue :
      brightonPossessionOutcomeClosed ≡ true
    chapelHillPossessionOutcomeClosed : Bool
    chapelHillPossessionOutcomeClosedIsTrue :
      chapelHillPossessionOutcomeClosed ≡ true
    herriesPrimaryPossessionCarrierRecoveredHere : Bool
    herriesPrimaryPossessionCarrierRecoveredHereIsFalse :
      herriesPrimaryPossessionCarrierRecoveredHere ≡ false

recoveredPossessionOrderFixture : RecoveredPossessionOrderFixture
recoveredPossessionOrderFixture =
  recoveredPossessionOrderFixture
    brightonPossessionOrder
    chapelHillPossessionOrder
    true refl
    true refl
    false refl
