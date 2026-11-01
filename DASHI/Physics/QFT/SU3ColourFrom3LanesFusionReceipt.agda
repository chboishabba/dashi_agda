module DASHI.Physics.QFT.SU3ColourFrom3LanesFusionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt as Conditional
import DASHI.Physics.QFT.FinitePrimeLaneDHRSMCompatibilityLedger as Ledger

------------------------------------------------------------------------
-- SU(3) colour from three-lane fusion diagnostic.
--
-- This receipt records a candidate route, not a promotion:
--
--   * the three quark/prime lanes span a 3-dimensional carrier space;
--   * the Weyl group of SU(3) is S3, matching discrete permutations of
--     the three lane labels;
--   * full continuous SU(3) colour would require the carrier metric on
--     this 3-lane space to be SU(3)-invariant;
--   * the current lane weights/masses are not equal, so the metric is not
--     SU(3)-invariant as stated.  Exact colour is therefore blocked on a
--     metric/chiral-limit receipt.
--
-- No exact SU(3)_c, G_DHR ~= G_SM, or terminal promotion is introduced.

data ThreeLaneCarrierBasis : Set where
  p2Basis :
    ThreeLaneCarrierBasis

  p3Basis :
    ThreeLaneCarrierBasis

  p5Basis :
    ThreeLaneCarrierBasis

canonicalThreeLaneBasis :
  List ThreeLaneCarrierBasis
canonicalThreeLaneBasis =
  p2Basis
  ∷ p3Basis
  ∷ p5Basis
  ∷ []

threeLaneCarrierDimension : Nat
threeLaneCarrierDimension =
  3

data SU3WeylGroup : Set where
  S3 :
    SU3WeylGroup

data ThreeLanePermutationGroup : Set where
  lanePermutationS3 :
    ThreeLanePermutationGroup

data CarrierMetricStatus : Set where
  laneWeightsDifferMetricNotSU3Invariant :
    CarrierMetricStatus

data SU3ColourFrom3LanesFusionStatus : Set where
  candidateBlockedOnMetricChiralLimit :
    SU3ColourFrom3LanesFusionStatus

metricObstructionLabel : String
metricObstructionLabel =
  "The current carrier metric is not SU(3)-invariant because p2, p3, and p5 lane weights/masses differ"

chiralLimitBoundaryLabel : String
chiralLimitBoundaryLabel =
  "A full SU(3)_c result would require an SU(3)-invariant metric, plausibly only after a chiral-limit or metric-renormalisation receipt"

candidateOnlyBoundaryLabel : String
candidateOnlyBoundaryLabel =
  "The S3 Weyl/permutation match is a finite candidate diagnostic and does not promote exact continuous SU(3)_c"

record SU3ColourFrom3LanesFusionReceipt : Setω where
  field
    status :
      SU3ColourFrom3LanesFusionStatus

    p2Lane :
      Ledger.FinitePrimeLaneSMRow

    p2LaneIsCanonical :
      p2Lane ≡ Ledger.p2U1YFinitePrimeLaneSMRow

    p3Lane :
      Ledger.FinitePrimeLaneSMRow

    p3LaneIsCanonical :
      p3Lane ≡ Ledger.p3SU2LFinitePrimeLaneSMRow

    p5Lane :
      Ledger.FinitePrimeLaneSMRow

    p5LaneIsCanonical :
      p5Lane ≡ Ledger.p5SU3cFinitePrimeLaneSMRow

    threeLaneCarrierBasis :
      List ThreeLaneCarrierBasis

    threeLaneCarrierBasisIsCanonical :
      threeLaneCarrierBasis ≡ canonicalThreeLaneBasis

    threeLaneCarrierSpaceDimension :
      Nat

    threeLaneCarrierSpaceDimensionIsThree :
      threeLaneCarrierSpaceDimension ≡ threeLaneCarrierDimension

    threeLaneSpaceIsC3 :
      Bool

    threeLaneSpaceIsC3IsTrue :
      threeLaneSpaceIsC3 ≡ true

    su3WeylGroup :
      SU3WeylGroup

    su3WeylGroupIsS3 :
      su3WeylGroup ≡ S3

    discreteLanePermutationGroup :
      ThreeLanePermutationGroup

    discreteLanePermutationGroupIsS3 :
      discreteLanePermutationGroup ≡ lanePermutationS3

    su3WeylMatchesLanePermutation :
      Bool

    su3WeylMatchesLanePermutationIsTrue :
      su3WeylMatchesLanePermutation ≡ true

    currentMetricStatus :
      CarrierMetricStatus

    currentMetricStatusIsObstructed :
      currentMetricStatus ≡ laneWeightsDifferMetricNotSU3Invariant

    laneWeightsUniform :
      Bool

    laneWeightsUniformIsFalse :
      laneWeightsUniform ≡ false

    su3InvariantCarrierMetric :
      Bool

    su3InvariantCarrierMetricIsFalse :
      su3InvariantCarrierMetric ≡ false

    fullSU3ColourDerived :
      Bool

    fullSU3ColourDerivedIsFalse :
      fullSU3ColourDerived ≡ false

    su3ColourFromLaneFusionCandidate :
      Bool

    su3ColourFromLaneFusionCandidateIsTrue :
      su3ColourFromLaneFusionCandidate ≡ true

    su3ColourBlockedOnMetric :
      Bool

    su3ColourBlockedOnMetricIsTrue :
      su3ColourBlockedOnMetric ≡ true

    chiralLimitCandidate :
      Bool

    chiralLimitCandidateIsTrue :
      chiralLimitCandidate ≡ true

    exactSU3cPromoted :
      Bool

    exactSU3cPromotedIsFalse :
      exactSU3cPromoted ≡ false

    exactGDHREqualsGSMPromoted :
      Bool

    exactGDHREqualsGSMPromotedIsFalse :
      exactGDHREqualsGSMPromoted ≡ false

    existingConditionalReceipt :
      Conditional.ConditionalGDHRSMPromotionReceipt

    existingUnconditionalGDHREqualsGSMPromotedIsFalse :
      Conditional.ConditionalGDHRSMPromotionReceipt.unconditionalGDHREqualsGSMPromoted
        existingConditionalReceipt
      ≡
      false

    metricObstruction :
      String

    metricObstructionIsCanonical :
      metricObstruction ≡ metricObstructionLabel

    chiralLimitBoundary :
      String

    chiralLimitBoundaryIsCanonical :
      chiralLimitBoundary ≡ chiralLimitBoundaryLabel

    candidateOnlyBoundary :
      String

    candidateOnlyBoundaryIsCanonical :
      candidateOnlyBoundary ≡ candidateOnlyBoundaryLabel

    receiptBoundary :
      List String

open SU3ColourFrom3LanesFusionReceipt public

canonicalSU3ColourFrom3LanesFusionReceipt :
  SU3ColourFrom3LanesFusionReceipt
canonicalSU3ColourFrom3LanesFusionReceipt =
  record
    { status =
        candidateBlockedOnMetricChiralLimit
    ; p2Lane =
        Ledger.p2U1YFinitePrimeLaneSMRow
    ; p2LaneIsCanonical =
        refl
    ; p3Lane =
        Ledger.p3SU2LFinitePrimeLaneSMRow
    ; p3LaneIsCanonical =
        refl
    ; p5Lane =
        Ledger.p5SU3cFinitePrimeLaneSMRow
    ; p5LaneIsCanonical =
        refl
    ; threeLaneCarrierBasis =
        canonicalThreeLaneBasis
    ; threeLaneCarrierBasisIsCanonical =
        refl
    ; threeLaneCarrierSpaceDimension =
        threeLaneCarrierDimension
    ; threeLaneCarrierSpaceDimensionIsThree =
        refl
    ; threeLaneSpaceIsC3 =
        true
    ; threeLaneSpaceIsC3IsTrue =
        refl
    ; su3WeylGroup =
        S3
    ; su3WeylGroupIsS3 =
        refl
    ; discreteLanePermutationGroup =
        lanePermutationS3
    ; discreteLanePermutationGroupIsS3 =
        refl
    ; su3WeylMatchesLanePermutation =
        true
    ; su3WeylMatchesLanePermutationIsTrue =
        refl
    ; currentMetricStatus =
        laneWeightsDifferMetricNotSU3Invariant
    ; currentMetricStatusIsObstructed =
        refl
    ; laneWeightsUniform =
        false
    ; laneWeightsUniformIsFalse =
        refl
    ; su3InvariantCarrierMetric =
        false
    ; su3InvariantCarrierMetricIsFalse =
        refl
    ; fullSU3ColourDerived =
        false
    ; fullSU3ColourDerivedIsFalse =
        refl
    ; su3ColourFromLaneFusionCandidate =
        true
    ; su3ColourFromLaneFusionCandidateIsTrue =
        refl
    ; su3ColourBlockedOnMetric =
        true
    ; su3ColourBlockedOnMetricIsTrue =
        refl
    ; chiralLimitCandidate =
        true
    ; chiralLimitCandidateIsTrue =
        refl
    ; exactSU3cPromoted =
        false
    ; exactSU3cPromotedIsFalse =
        refl
    ; exactGDHREqualsGSMPromoted =
        false
    ; exactGDHREqualsGSMPromotedIsFalse =
        refl
    ; existingConditionalReceipt =
        Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; existingUnconditionalGDHREqualsGSMPromotedIsFalse =
        refl
    ; metricObstruction =
        metricObstructionLabel
    ; metricObstructionIsCanonical =
        refl
    ; chiralLimitBoundary =
        chiralLimitBoundaryLabel
    ; chiralLimitBoundaryIsCanonical =
        refl
    ; candidateOnlyBoundary =
        candidateOnlyBoundaryLabel
    ; candidateOnlyBoundaryIsCanonical =
        refl
    ; receiptBoundary =
        "The p2/p3/p5 rows are recorded as a 3-dimensional carrier space"
        ∷ "The Weyl group of SU(3) is recorded as S3, matching discrete lane permutations"
        ∷ "The present lane metric is not SU(3)-invariant because lane weights/masses differ"
        ∷ "Exact SU(3)_c is blocked until an SU(3)-invariant carrier metric is derived, plausibly through a chiral-limit or metric-renormalisation receipt"
        ∷ "This receipt is candidate-only and keeps exact SU(3)_c and G_DHR ~= G_SM false"
        ∷ []
    }

su3ColourFrom3LanesCarrierDimensionIsThree :
  threeLaneCarrierSpaceDimension canonicalSU3ColourFrom3LanesFusionReceipt
  ≡
  3
su3ColourFrom3LanesCarrierDimensionIsThree =
  refl

su3ColourFrom3LanesWeylGroupIsS3 :
  su3WeylGroup canonicalSU3ColourFrom3LanesFusionReceipt
  ≡
  S3
su3ColourFrom3LanesWeylGroupIsS3 =
  refl

su3ColourFrom3LanesPermutationGroupIsS3 :
  discreteLanePermutationGroup canonicalSU3ColourFrom3LanesFusionReceipt
  ≡
  lanePermutationS3
su3ColourFrom3LanesPermutationGroupIsS3 =
  refl

su3ColourFrom3LanesMetricNotInvariant :
  su3InvariantCarrierMetric canonicalSU3ColourFrom3LanesFusionReceipt
  ≡
  false
su3ColourFrom3LanesMetricNotInvariant =
  refl

su3ColourFrom3LanesBlockedOnMetric :
  su3ColourBlockedOnMetric canonicalSU3ColourFrom3LanesFusionReceipt
  ≡
  true
su3ColourFrom3LanesBlockedOnMetric =
  refl

su3ColourFrom3LanesCandidateOnly :
  su3ColourFromLaneFusionCandidate canonicalSU3ColourFrom3LanesFusionReceipt
  ≡
  true
su3ColourFrom3LanesCandidateOnly =
  refl

su3ColourFrom3LanesExactSU3cPromotedFalse :
  exactSU3cPromoted canonicalSU3ColourFrom3LanesFusionReceipt
  ≡
  false
su3ColourFrom3LanesExactSU3cPromotedFalse =
  refl

su3ColourFrom3LanesExactGDHREqualsGSMPromotedFalse :
  exactGDHREqualsGSMPromoted canonicalSU3ColourFrom3LanesFusionReceipt
  ≡
  false
su3ColourFrom3LanesExactGDHREqualsGSMPromotedFalse =
  refl
