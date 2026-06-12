module DASHI.Physics.Closure.Paper0SharedMarginDependencyReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.FullUnificationPublicationRoadmapReceipt as Roadmap
import DASHI.Physics.Closure.StrictMarginImpliesAbsorptionReceipt as L0

------------------------------------------------------------------------
-- Paper 0 shared margin dependency receipt.
--
-- This receipt is a small publication-lane adapter.  It makes explicit that
-- Paper 0 depends only on the shared fail-closed margin grammar and on the
-- roadmap ordering that places that grammar before NS, Gate 3, YM, and full
-- unification papers.  It deliberately introduces no new theorem content.

data Paper0DependencyStatus : Set where
  paper0SharedMarginDependencyRecordedFailClosed :
    Paper0DependencyStatus

data Paper0L0Stage : Set where
  l0Point1DynamicsBound :
    Paper0L0Stage

  l0Point2RatioSignedEquivalence :
    Paper0L0Stage

  l0Point3StrictMarginAbsorption :
    Paper0L0Stage

  l0Point4FailClosedNonPromotion :
    Paper0L0Stage

canonicalPaper0L0Stages :
  List Paper0L0Stage
canonicalPaper0L0Stages =
  l0Point1DynamicsBound
  ∷ l0Point2RatioSignedEquivalence
  ∷ l0Point3StrictMarginAbsorption
  ∷ l0Point4FailClosedNonPromotion
  ∷ []

data Paper0ClaimBoundary : Set where
  sharedGrammarOnly :
    Paper0ClaimBoundary

  noLaneSpecificAnalyticInhabitant :
    Paper0ClaimBoundary

  candidateLaneSpecificAnalyticsOnly :
    Paper0ClaimBoundary

  noNSRegularity :
    Paper0ClaimBoundary

  noGate3ContinuumLift :
    Paper0ClaimBoundary

  noYMMassGap :
    Paper0ClaimBoundary

  noClayOrTerminalPromotion :
    Paper0ClaimBoundary

canonicalPaper0ClaimBoundaries :
  List Paper0ClaimBoundary
canonicalPaper0ClaimBoundaries =
  sharedGrammarOnly
  ∷ noLaneSpecificAnalyticInhabitant
  ∷ candidateLaneSpecificAnalyticsOnly
  ∷ noNSRegularity
  ∷ noGate3ContinuumLift
  ∷ noYMMassGap
  ∷ noClayOrTerminalPromotion
  ∷ []

data Paper0AnalyticsScope : Set where
  paper0LaneSpecificAnalyticsCandidateScopeOnly :
    Paper0AnalyticsScope

canonicalPaper0AnalyticsScope :
  Paper0AnalyticsScope
canonicalPaper0AnalyticsScope =
  paper0LaneSpecificAnalyticsCandidateScopeOnly

data Paper0DependencyPromotion : Set where

paper0DependencyPromotionImpossibleHere :
  Paper0DependencyPromotion →
  ⊥
paper0DependencyPromotionImpossibleHere ()

paper0DependencyStatement :
  String
paper0DependencyStatement =
  "Paper 0 is the publishable shared margin grammar dependency: it records L0.1 dynamics-bound obligation, L0.2 ratio/signed equivalence with A>0, L0.3 strict-margin absorption, and L0.4 fail-closed non-promotion. It supplies no NS, Gate 3, YM, Clay, or terminal promotion."

record Paper0SharedMarginDependencyReceipt : Setω where
  field
    status :
      Paper0DependencyStatus

    statusIsFailClosed :
      status ≡ paper0SharedMarginDependencyRecordedFailClosed

    l0Receipt :
      L0.StrictMarginImpliesAbsorptionReceipt

    roadmapReceipt :
      Roadmap.FullUnificationPublicationRoadmapReceipt

    l0Stages :
      List Paper0L0Stage

    l0StagesAreCanonical :
      l0Stages ≡ canonicalPaper0L0Stages

    l0LemmasAreCanonical :
      L0.StrictMarginImpliesAbsorptionReceipt.lemmas l0Receipt
      ≡
      L0.canonicalL0Lemmas

    paper0IsFirstPublication :
      Roadmap.FullUnificationPublicationRoadmapReceipt.publicationOrder
        roadmapReceipt
      ≡
      Roadmap.canonicalPublicationOrder

    paper0MarkedPublishable :
      Roadmap.FullUnificationPublicationRoadmapReceipt.paperZeroPublishableNow
        roadmapReceipt
      ≡
      true

    downstreamNeedsAnalyticInhabitants :
      Roadmap.FullUnificationPublicationRoadmapReceipt.downstreamPapersNeedAnalyticInhabitants
        roadmapReceipt
      ≡
      true

    l0ClayPromotionFalse :
      L0.StrictMarginImpliesAbsorptionReceipt.clayPromotion l0Receipt
      ≡
      false

    l0NSRegularityFalse :
      L0.StrictMarginImpliesAbsorptionReceipt.provesNSRegularity l0Receipt
      ≡
      false

    l0YMMassGapFalse :
      L0.StrictMarginImpliesAbsorptionReceipt.provesYMMassGap l0Receipt
      ≡
      false

    l0Gate3LiftFalse :
      L0.StrictMarginImpliesAbsorptionReceipt.provesGate3ContinuumLift
        l0Receipt
      ≡
      false

    claimBoundaries :
      List Paper0ClaimBoundary

    claimBoundariesAreCanonical :
      claimBoundaries ≡ canonicalPaper0ClaimBoundaries

    analyticsScope :
      Paper0AnalyticsScope

    analyticsScopeIsCanonical :
      analyticsScope ≡ canonicalPaper0AnalyticsScope

    sharedGrammarOnlyClaim :
      Bool

    sharedGrammarOnlyClaimIsTrue :
      sharedGrammarOnlyClaim ≡ true

    laneSpecificAnalyticsProvided :
      Bool

    laneSpecificAnalyticsProvidedIsFalse :
      laneSpecificAnalyticsProvided ≡ false

    paper0LaneSpecificAnalyticsCandidateProvided :
      Bool

    paper0LaneSpecificAnalyticsCandidateProvidedIsTrue :
      paper0LaneSpecificAnalyticsCandidateProvided ≡ true

    nsRegularityPromoted :
      Bool

    nsRegularityPromotedIsFalse :
      nsRegularityPromoted ≡ false

    gate3ContinuumLiftPromoted :
      Bool

    gate3ContinuumLiftPromotedIsFalse :
      gate3ContinuumLiftPromoted ≡ false

    ymMassGapPromoted :
      Bool

    ymMassGapPromotedIsFalse :
      ymMassGapPromoted ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    promotionFlags :
      List Paper0DependencyPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ paper0DependencyStatement

    receiptBoundary :
      List String

open Paper0SharedMarginDependencyReceipt public

canonicalPaper0SharedMarginDependencyReceipt :
  Paper0SharedMarginDependencyReceipt
canonicalPaper0SharedMarginDependencyReceipt =
  record
    { status =
        paper0SharedMarginDependencyRecordedFailClosed
    ; statusIsFailClosed =
        refl
    ; l0Receipt =
        L0.canonicalStrictMarginImpliesAbsorptionReceipt
    ; roadmapReceipt =
        Roadmap.canonicalFullUnificationPublicationRoadmapReceipt
    ; l0Stages =
        canonicalPaper0L0Stages
    ; l0StagesAreCanonical =
        refl
    ; l0LemmasAreCanonical =
        refl
    ; paper0IsFirstPublication =
        refl
    ; paper0MarkedPublishable =
        refl
    ; downstreamNeedsAnalyticInhabitants =
        refl
    ; l0ClayPromotionFalse =
        refl
    ; l0NSRegularityFalse =
        refl
    ; l0YMMassGapFalse =
        refl
    ; l0Gate3LiftFalse =
        refl
    ; claimBoundaries =
        canonicalPaper0ClaimBoundaries
    ; claimBoundariesAreCanonical =
        refl
    ; analyticsScope =
        canonicalPaper0AnalyticsScope
    ; analyticsScopeIsCanonical =
        refl
    ; sharedGrammarOnlyClaim =
        true
    ; sharedGrammarOnlyClaimIsTrue =
        refl
    ; laneSpecificAnalyticsProvided =
        false
    ; laneSpecificAnalyticsProvidedIsFalse =
        refl
    ; paper0LaneSpecificAnalyticsCandidateProvided =
        true
    ; paper0LaneSpecificAnalyticsCandidateProvidedIsTrue =
        refl
    ; nsRegularityPromoted =
        false
    ; nsRegularityPromotedIsFalse =
        refl
    ; gate3ContinuumLiftPromoted =
        false
    ; gate3ContinuumLiftPromotedIsFalse =
        refl
    ; ymMassGapPromoted =
        false
    ; ymMassGapPromotedIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        paper0DependencyStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Paper 0 depends on StrictMarginImpliesAbsorptionReceipt and the publication roadmap"
        ∷ "L0.1-L0.4 are explicit publication stages"
        ∷ "Paper 0 is shared grammar only; downstream analytic inhabitants remain open"
        ∷ "Paper 0 carries a bounded candidate-only lane-specific analytics scope, but not a promoted analytic claim"
        ∷ "No NS, Gate 3, YM, Clay, or terminal promotion follows"
        ∷ []
    }

paper0DependencyClayPromotionFalse :
  clayPromotion canonicalPaper0SharedMarginDependencyReceipt
  ≡
  false
paper0DependencyClayPromotionFalse =
  refl

paper0DependencyPromotionFlagsEmpty :
  promotionFlags canonicalPaper0SharedMarginDependencyReceipt
  ≡
  []
paper0DependencyPromotionFlagsEmpty =
  refl

paper0LaneSpecificAnalyticsCandidateProvidedWitnessIsTrue :
  paper0LaneSpecificAnalyticsCandidateProvided
    canonicalPaper0SharedMarginDependencyReceipt
  ≡
  true
paper0LaneSpecificAnalyticsCandidateProvidedWitnessIsTrue =
  refl
