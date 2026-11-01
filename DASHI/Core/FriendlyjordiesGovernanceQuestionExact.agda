module DASHI.Core.FriendlyjordiesGovernanceQuestionExact where

------------------------------------------------------------------------
-- Named March-2026 application surface.
--
-- This module records the *question* that motivated
-- GovernanceTrajectoryRealisationExact without assigning a winner.
-- Historical/empirical assertions must arrive later as source-revision
-- witnesses; labels here do not constitute evidence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.String using (String)

import DASHI.Core.GovernanceTrajectoryRealisationExact as Gov

data AustralianPoliticalFormation : Set where
  labor greens : AustralianPoliticalFormation

data MarchCase : Set where
  cprs2009 southAustraliaRenewables : MarchCase

data ComparisonHorizon : Set where
  immediate longRun : ComparisonHorizon

record MarchGovernanceQuestion : Set where
  constructor march-governance-question
  field
    leftFormation : AustralianPoliticalFormation
    rightFormation : AustralianPoliticalFormation
    cases : List MarchCase
    horizons : List ComparisonHorizon
    sourceWitnessRequired : Bool
    sourceWitnessRequiredIsTrue : sourceWitnessRequired ≡ true
    counterfactualWitnessRequired : Bool
    counterfactualWitnessRequiredIsTrue :
      counterfactualWitnessRequired ≡ true
    universalRankingEncoded : Bool
    universalRankingEncodedIsFalse : universalRankingEncoded ≡ false

open MarchGovernanceQuestion public

canonicalMarchGovernanceQuestion : MarchGovernanceQuestion
canonicalMarchGovernanceQuestion =
  march-governance-question
    labor
    greens
    (cprs2009 ∷ southAustraliaRenewables ∷ [])
    (immediate ∷ longRun ∷ [])
    true refl
    true refl
    false refl

record HistoricalCaseEvidence : Set where
  constructor historical-case-evidence
  field
    case : MarchCase
    sourceRevisionRef : String
    statementRef : String
    provenanceRefs : List String
    evidenceKind : Gov.EvidenceKind
    sourceChecked : Bool
    sourceCheckedIsTrue : sourceChecked ≡ true

open HistoricalCaseEvidence public

-- The atlas deliberately exposes no constructor
--   canonicalMarchGovernanceQuestion -> ScopedComparativeClaim
-- because the named question alone supplies no gap estimates or ordering proof.

record FriendlyjordiesGovernanceBoundary : Set where
  constructor friendlyjordies-governance-boundary
  field
    namesAreQuestionCoordinatesOnly : Bool
    namesAreQuestionCoordinatesOnlyIsTrue :
      namesAreQuestionCoordinatesOnly ≡ true
    sourceFreeRankingPossible : Bool
    sourceFreeRankingPossibleIsFalse :
      sourceFreeRankingPossible ≡ false

canonicalFriendlyjordiesGovernanceBoundary :
  FriendlyjordiesGovernanceBoundary
canonicalFriendlyjordiesGovernanceBoundary =
  friendlyjordies-governance-boundary
    true refl
    false refl
