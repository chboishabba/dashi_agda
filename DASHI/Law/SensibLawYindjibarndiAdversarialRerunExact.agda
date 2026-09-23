module DASHI.Law.SensibLawYindjibarndiAdversarialRerunExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawAdversarialProofSearchRuntimeExact as Search
import DASHI.Law.SensibLawReviewedTreatmentProofGraphBridgeExact as Bridge
import DASHI.Law.SensibLawYindjibarndiEmpiricalAuthorityJoinExact as Y
import DASHI.Law.SensibLawSharedWorldConsumerJoinExact as Join

------------------------------------------------------------------------
-- M8.1 / S20.11 YINDJIBARNDI ADVERSARIAL RERUN
--
-- The empirical packet has:
--   1 support treatment;
--   2 live Yunupingu scope/defeater treatments;
--   1 Mabo-specific defeater;
--   1 Mabo-specific counter-defeater.
--
-- The exact-coordinate counter-defeater can pay the single Mabo target, but
-- it cannot erase the two separate Yunupingu objections.  Therefore the
-- route remains defeated/contested and must search counter-defeaters again.
------------------------------------------------------------------------

data DefeaterIdentity : Set where
  stateYunupinguScope : DefeaterIdentity
  fmgYunupinguScope : DefeaterIdentity
  fmgMaboAcquisition : DefeaterIdentity

data CounterIdentity : Set where
  applicantMaboDistinction : CounterIdentity

data ActiveDefeaters : Set where
  threeActive : ActiveDefeaters
  twoYunupinguActive : ActiveDefeaters

applyApplicantMaboDistinction :
  ActiveDefeaters → ActiveDefeaters
applyApplicantMaboDistinction threeActive = twoYunupinguActive
applyApplicantMaboDistinction twoYunupinguActive = twoYunupinguActive

maboCounterLeavesYunupinguObjections :
  applyApplicantMaboDistinction threeActive ≡ twoYunupinguActive
maboCounterLeavesYunupinguObjections = refl

routeStateAfterMaboCounter : Search.RouteState
routeStateAfterMaboCounter = Search.defeated

routeStillSearchesCounterDefeater :
  Search.nextRole routeStateAfterMaboCounter
  ≡ Search.counterDefeaterSearch
routeStillSearchesCounterDefeater =
  Search.defeatedSearchesCounterDefeater

------------------------------------------------------------------------
-- Role compilation is inherited from the generic bridge.
------------------------------------------------------------------------

applicantSupportRole :
  Bridge.searchRole Bridge.supportTreatment ≡ Search.supportSearch
applicantSupportRole = refl

stateScopeRole :
  Bridge.searchRole Bridge.authorityScopeTreatment
  ≡ Search.counterDefeaterSearch
stateScopeRole = refl

fmgDefeaterRole :
  Bridge.searchRole Bridge.defeaterTreatment
  ≡ Search.defeaterSearch
fmgDefeaterRole = refl

applicantCounterRole :
  Bridge.searchRole Bridge.counterDefeaterTreatment
  ≡ Search.counterDefeaterSearch
applicantCounterRole = refl

------------------------------------------------------------------------
-- Shared-world exactness remains the precondition.
------------------------------------------------------------------------

yunupinguExactJoinExists :
  Join.ReviewedJoinWitness
    Y.yunupinguAcquisitionCoordinate
    Y.yindjibarndiEmpiricalSlice
yunupinguExactJoinExists =
  Y.yunupinguReviewedJoin

maboExactJoinExists :
  Join.ReviewedJoinWitness
    Y.maboAcquisitionDistinctionCoordinate
    Y.yindjibarndiEmpiricalSlice
maboExactJoinExists =
  Y.maboSpecificTreatmentReviewedJoin

data GenericMaboJoinPaysRoute : Set where

genericMaboStillCannotPay :
  GenericMaboJoinPaysRoute → ⊥
genericMaboStillCannotPay ()

------------------------------------------------------------------------
-- Acceptance boundary.
------------------------------------------------------------------------

record YindjibarndiRerunBoundary : Set where
  constructor yindjibarndiRerunBoundary
  field
    exactYunupinguCoordinateReused : Bool
    exactYunupinguCoordinateReusedIsTrue :
      exactYunupinguCoordinateReused ≡ true

    exactMaboCoordinateReused : Bool
    exactMaboCoordinateReusedIsTrue :
      exactMaboCoordinateReused ≡ true

    maboCounterErasesAllDefeaters : Bool
    maboCounterErasesAllDefeatersIsFalse :
      maboCounterErasesAllDefeaters ≡ false

    yunupinguScopeObjectionsRemainLive : Bool
    yunupinguScopeObjectionsRemainLiveIsTrue :
      yunupinguScopeObjectionsRemainLive ≡ true

    rerunSearchesCounterDefeatersAgain : Bool
    rerunSearchesCounterDefeatersAgainIsTrue :
      rerunSearchesCounterDefeatersAgain ≡ true

    routeStatePredictsJudicialOutcome : Bool
    routeStatePredictsJudicialOutcomeIsFalse :
      routeStatePredictsJudicialOutcome ≡ false

open YindjibarndiRerunBoundary public

canonicalYindjibarndiRerunBoundary : YindjibarndiRerunBoundary
canonicalYindjibarndiRerunBoundary =
  yindjibarndiRerunBoundary
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
