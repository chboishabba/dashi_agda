module DASHI.Cognition.PNF.SensibLawAdjudicativeTemporalNonRetroactivityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawIssueIndexedAdjudicativeHyperfabricExact as Issue

------------------------------------------------------------------------
-- Cross-pollinated from #705 TemporalAuthorityNonRetroactivityExact:
-- later evidence may refine a later adjudicative snapshot but cannot become the
-- historical producer of an earlier burden/standard/evidence closure.
------------------------------------------------------------------------

data SnapshotOrder : Set where before sameTime after : SnapshotOrder

data AdjudicativeSnapshotStage : Set where
  pleadingsSnapshot
  evidenceSnapshot
  hearingSnapshot
  decisionSnapshot
  appealSnapshot
  laterDiscoverySnapshot
  : AdjudicativeSnapshotStage

record AdjudicativeSnapshot (issue : Issue.LegalIssue) : Set where
  constructor adjudicativeSnapshot
  field
    stage : AdjudicativeSnapshotStage
    timeReference : String
    burdenAvailable : Bool
    standardAvailable : Bool
    evidenceAvailable : Bool
    authorityAvailable : Bool
    jurisdictionAvailable : Bool
    decisionReference : String
    snapshotReference : String

open AdjudicativeSnapshot public

record LaterEvidenceClaim {issue : Issue.LegalIssue}
    (earlier later : AdjudicativeSnapshot issue) : Set where
  constructor laterEvidenceClaim
  field
    relation : SnapshotOrder
    laterEvidenceReference : String
    claimsEarlierBurdenSatisfied : Bool
    claimsEarlierStandardSatisfied : Bool
    claimsEarlierEvidenceSatisfied : Bool

open LaterEvidenceClaim public

record RetroactiveAdjudicativePromotion {issue : Issue.LegalIssue}
    {earlier later : AdjudicativeSnapshot issue}
    (claim : LaterEvidenceClaim earlier later) : Set where
  constructor retroactiveAdjudicativePromotion
  field
    evidenceCameAfter : relation claim ≡ after
    claimsEarlierClosure :
      claimsEarlierBurdenSatisfied claim ≡ true
      × claimsEarlierStandardSatisfied claim ≡ true
      × claimsEarlierEvidenceSatisfied claim ≡ true

open RetroactiveAdjudicativePromotion public

------------------------------------------------------------------------
-- Later snapshot refinement is allowed without rewriting earlier history.
------------------------------------------------------------------------

record SnapshotRefinement {issue : Issue.LegalIssue}
    (earlier later : AdjudicativeSnapshot issue) : Set where
  constructor snapshotRefinement
  field
    chronology : SnapshotOrder
    laterMayAddEvidence : Bool
    laterMayAddEvidenceIsTrue : laterMayAddEvidence ≡ true
    earlierSnapshotRewritten : Bool
    earlierSnapshotRewrittenIsFalse : earlierSnapshotRewritten ≡ false
    refinementReference : String

open SnapshotRefinement public

------------------------------------------------------------------------
-- Reverse temporal obligation.
------------------------------------------------------------------------

data HistoricalAdjudicativeQuestion : Set where
  whatBurdenWasAvailable
  whatStandardWasAvailable
  whatEvidenceWasAvailable
  whatAuthorityWasAvailable
  whatJurisdictionWasAvailable
  : HistoricalAdjudicativeQuestion

data HistoricalProducer : Set where
  burdenAtTimeProducer
  standardAtTimeProducer
  evidenceAtTimeProducer
  authorityAtTimeProducer
  jurisdictionAtTimeProducer
  : HistoricalProducer

reverseHistoricalQuestion : HistoricalAdjudicativeQuestion → HistoricalProducer
reverseHistoricalQuestion whatBurdenWasAvailable = burdenAtTimeProducer
reverseHistoricalQuestion whatStandardWasAvailable = standardAtTimeProducer
reverseHistoricalQuestion whatEvidenceWasAvailable = evidenceAtTimeProducer
reverseHistoricalQuestion whatAuthorityWasAvailable = authorityAtTimeProducer
reverseHistoricalQuestion whatJurisdictionWasAvailable = jurisdictionAtTimeProducer

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data LaterEvidenceRetroactivelySatisfiesEarlierBurden : Set where
data LaterFindingRetroactivelySatisfiesEarlierStandard : Set where
data AppealSnapshotRewritesTrialEvidenceHistory : Set where
data LaterAuthorityRetroactivelyBecomesEarlierAuthority : Set where

laterEvidenceDoesNotRetroactivelySatisfyBurden :
  LaterEvidenceRetroactivelySatisfiesEarlierBurden → ⊥
laterEvidenceDoesNotRetroactivelySatisfyBurden ()

laterFindingDoesNotRetroactivelySatisfyStandard :
  LaterFindingRetroactivelySatisfiesEarlierStandard → ⊥
laterFindingDoesNotRetroactivelySatisfyStandard ()

appealDoesNotRewriteTrialEvidenceHistory :
  AppealSnapshotRewritesTrialEvidenceHistory → ⊥
appealDoesNotRewriteTrialEvidenceHistory ()

laterAuthorityDoesNotBecomeEarlierAuthority :
  LaterAuthorityRetroactivelyBecomesEarlierAuthority → ⊥
laterAuthorityDoesNotBecomeEarlierAuthority ()

record AdjudicativeTemporalBoundary : Set where
  constructor adjudicative-temporal-boundary
  field
    laterEvidenceMayRefineLaterSnapshot : Bool
    laterEvidenceRewritesEarlierSnapshot : Bool
    laterEvidenceRetroactivelyPaysEarlierBurden : Bool
    laterFindingRetroactivelyPaysEarlierStandard : Bool
    historicalQuestionRoutesToTimeIndexedProducer : Bool

canonicalAdjudicativeTemporalBoundary : AdjudicativeTemporalBoundary
canonicalAdjudicativeTemporalBoundary =
  adjudicative-temporal-boundary true false false false true
