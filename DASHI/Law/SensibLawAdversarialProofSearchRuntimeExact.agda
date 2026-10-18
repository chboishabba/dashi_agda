module DASHI.Law.SensibLawAdversarialProofSearchRuntimeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawDialecticalProofSearchExact as Dialectic
import DASHI.Law.SensibLawBidirectionalWorldLawProofSearchExact as Bidi
import DASHI.Law.SensibLawPabaiDefeaterRefinementRerunExact as Pabai
import DASHI.Law.SensibLawMaboPabaiExecutableProofSearchExact as MaboPabai
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawFiniteLegalSearchRegressionExact as Regression
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence

------------------------------------------------------------------------
-- S20 ADVERSARIAL LEGAL PROOF SEARCH RUNTIME
--
-- Existing law owners already provide support/defeater/comparator search,
-- world<->law bidi demands, and the Pabai proof -> defeat -> repair specimen.
-- This owner pins their orchestration law: support does not terminate
-- adversarial search; reviewed defeat may close one route; repair is only a
-- candidate and must face defeater search again.
------------------------------------------------------------------------

data RouteState : Set where
  missingAtoms : RouteState
  reachableCandidate : RouteState
  contested : RouteState
  defeated : RouteState
  reopenedCandidate : RouteState

data AdversarialRole : Set where
  supportSearch : AdversarialRole
  defeaterSearch : AdversarialRole
  counterDefeaterSearch : AdversarialRole
  comparatorSearch : AdversarialRole
  contradictionSearch : AdversarialRole
  authorityTreatmentSearch : AdversarialRole
  wrongTypeDiscriminatorSearch : AdversarialRole

nextRole : RouteState → AdversarialRole
nextRole missingAtoms = supportSearch
nextRole reachableCandidate = defeaterSearch
nextRole contested = counterDefeaterSearch
nextRole defeated = counterDefeaterSearch
nextRole reopenedCandidate = defeaterSearch

reachableStillSearchesDefeater :
  nextRole reachableCandidate ≡ defeaterSearch
reachableStillSearchesDefeater = refl

defeatedSearchesCounterDefeater :
  nextRole defeated ≡ counterDefeaterSearch
defeatedSearchesCounterDefeater = refl

reopenedSearchesDefeaterAgain :
  nextRole reopenedCandidate ≡ defeaterSearch
reopenedSearchesDefeaterAgain = refl

------------------------------------------------------------------------
-- Existing exact Pabai rerun witnesses the semantic transitions.
------------------------------------------------------------------------

pabaiReachableBefore :
  Search.reachable 1
    Regression.pabaiGraph
    Pabai.pabaiFactsBeforeDefeater
    Negligence.dutyProposition
  ≡ true
pabaiReachableBefore =
  Pabai.pabaiReachableBeforeDefeater

pabaiDefeatedAfterReviewedDefeater :
  Search.reachable 1
    Regression.pabaiGraph
    Pabai.pabaiFactsAfterDefeater
    Negligence.dutyProposition
  ≡ false
pabaiDefeatedAfterReviewedDefeater =
  Pabai.pabaiUnreachableAfterDefeater

pabaiRepairCandidateExists :
  Search.firstReopeningTransformation 1
    Negligence.dutyProposition
    (Regression.pabaiReformulationCandidate ∷ [])
  ≡ Search.found Regression.pabaiReformulationCandidate
pabaiRepairCandidateExists =
  Pabai.pabaiExistingRepairCandidateStillReopens

------------------------------------------------------------------------
-- Cross-domain firewall remains exact.
------------------------------------------------------------------------

maboAnalogyDoesNotTransferDoctrine :
  MaboPabai.MaboPabaiSearchBoundary.maboAnalogyAutomaticallyTransfersDoctrine
    MaboPabai.canonicalMaboPabaiSearchBoundary
  ≡ false
maboAnalogyDoesNotTransferDoctrine =
  MaboPabai.MaboPabaiSearchBoundary.maboAnalogyAutomaticallyTransfersDoctrineIsFalse
    MaboPabai.canonicalMaboPabaiSearchBoundary

dialecticalBoundary :
  Dialectic.DialecticalSearchBoundary
dialecticalBoundary =
  Dialectic.canonicalDialecticalSearchBoundary

bidiBoundary :
  Bidi.BidirectionalSearchBoundary
bidiBoundary =
  Bidi.canonicalBidirectionalSearchBoundary

data MoreSupportStopsDefeaterSearch : Set where
data ReopenedCandidateIsCurrentLaw : Set where
data StructuralAnalogyPaysWrongType : Set where
data SearchHitCreatesAdjudicativeTruth : Set where

supportCannotStopAdversarialSearch :
  MoreSupportStopsDefeaterSearch → ⊥
supportCannotStopAdversarialSearch ()

reopenedCandidateDoesNotBecomeCurrentLaw :
  ReopenedCandidateIsCurrentLaw → ⊥
reopenedCandidateDoesNotBecomeCurrentLaw ()

analogyCannotPayWrongType :
  StructuralAnalogyPaysWrongType → ⊥
analogyCannotPayWrongType ()

searchHitDoesNotCreateTruth :
  SearchHitCreatesAdjudicativeTruth → ⊥
searchHitDoesNotCreateTruth ()

record AdversarialProofSearchRuntimeBoundary : Set where
  constructor adversarialProofSearchRuntimeBoundary
  field
    supportAndDefeaterSearchRemainPaired : Bool
    supportAndDefeaterSearchRemainPairedIsTrue :
      supportAndDefeaterSearchRemainPaired ≡ true

    reviewedDefeaterMayCloseCandidateRoute : Bool
    reviewedDefeaterMayCloseCandidateRouteIsTrue :
      reviewedDefeaterMayCloseCandidateRoute ≡ true

    closedRouteMaySearchCounterDefeater : Bool
    closedRouteMaySearchCounterDefeaterIsTrue :
      closedRouteMaySearchCounterDefeater ≡ true

    reopenedRouteFacesDefeaterSearchAgain : Bool
    reopenedRouteFacesDefeaterSearchAgainIsTrue :
      reopenedRouteFacesDefeaterSearchAgain ≡ true

    structuralAnalogyAutomaticallyPaysSubstantiveRule : Bool
    structuralAnalogyAutomaticallyPaysSubstantiveRuleIsFalse :
      structuralAnalogyAutomaticallyPaysSubstantiveRule ≡ false

    adversarialSearchCreatesFinalJudgment : Bool
    adversarialSearchCreatesFinalJudgmentIsFalse :
      adversarialSearchCreatesFinalJudgment ≡ false

open AdversarialProofSearchRuntimeBoundary public

canonicalAdversarialProofSearchRuntimeBoundary :
  AdversarialProofSearchRuntimeBoundary
canonicalAdversarialProofSearchRuntimeBoundary =
  adversarialProofSearchRuntimeBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
